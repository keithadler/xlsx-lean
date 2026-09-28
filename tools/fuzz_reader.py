"""Throw broken files at xlsxlean and make sure it always answers.

    python tools/fuzz_reader.py SEED_DIR [--n 2000] [--seed 1] [--bin .lake/build/bin/xlsxlean]

Takes the .xlsx files in SEED_DIR, breaks them in many ways, and runs
`xlsxlean check --json` on each. An answer is a verdict or a clear "unreadable"; the
exit code is 0 or 1 and the output is JSON. Anything else is a failure of the reader:
a crash (a signal, or another exit code), output that is not JSON, or no answer
within the time limit. Failing inputs are kept in out/fuzz/failures.

The ways to break a file:
  flip        change a few bytes of the archive
  truncate    cut the archive short
  splice      glue the start of one archive to the end of another
  xml-*       open the archive, damage one XML entry, and write it back:
              cut, duplicate, unbalance tags, insert junk, huge numbers,
              deep nesting, entity and reference junk, a DTD, _xHHHH_ escapes
"""
import argparse, io, json, os, random, subprocess, sys, zipfile

def mutate_xml(rng, text):
    kind = rng.choice(["cut", "dup", "unbalance", "junk", "numbers", "deep", "entities", "dtd", "attrs", "xstring"])
    n = len(text)
    if n == 0:
        return kind, text
    a, b = sorted(rng.randrange(n + 1) for _ in range(2))
    if kind == "cut":
        return kind, text[:a] + text[b:]
    if kind == "dup":
        return kind, text[:b] + text[a:b] + text[b:]
    if kind == "unbalance":
        tag = rng.choice(["<row>", "</row>", "<c>", "</c>", "<v>", "</sheetData>", "<", ">", "/>"])
        return kind, text[:a] + tag + text[a:]
    if kind == "junk":
        junk = "".join(rng.choice("<>&\"'=/ \x00\x01\x7f￾\U0001F600abc0123") for _ in range(rng.randrange(1, 40)))
        return kind, text[:a] + junk + text[a:]
    if kind == "numbers":
        big = rng.choice(["99999999999999999999999999", "-1", "1e999", "4294967296", "18446744073709551616", "NaN", ""])
        import re
        return kind, re.sub(r'"\d+"', lambda m: f'"{big}"' if rng.random() < 0.3 else m.group(0), text)
    if kind == "deep":
        depth = rng.choice([1000, 10000, 100000])
        return kind, text[:a] + "<x>" * depth + "</x>" * depth + text[a:]
    if kind == "entities":
        ent = rng.choice(["&#0;", "&#x110000;", "&#xD800;", "&foo;", "&", "&#;", "&#x;", "&#99999999999;"])
        return kind, text[:a] + ent + text[a:]
    if kind == "dtd":
        return kind, '<!DOCTYPE x [<!ENTITY a "aaaa">]>' + text
    if kind == "xstring":
        esc = "".join(rng.choice(["_x0000_", "_xD800_", "_xDC00_", "_xD83D__xDE42_", "_xFFFF_", "_x005F_", "_x00", "_xZZZZ_", "_x000a_"])
                      for _ in range(rng.randrange(1, 4)))
        return kind, text[:a] + esc + text[a:]
    if kind == "attrs":
        import re
        return kind, re.sub(r'(\w+)="([^"]*)"', lambda m: f'{m.group(1)}="{m.group(2)}{rng.choice(["", ":", "Z99999999", "A0", "-5"])}"', text, count=rng.randrange(1, 20))
    return kind, text

def mutate(rng, data, others):
    kind = rng.choice(["flip", "truncate", "splice", "xml", "xml", "xml"])
    if kind == "flip":
        b = bytearray(data)
        for _ in range(rng.randrange(1, 12)):
            b[rng.randrange(len(b))] = rng.randrange(256)
        return "flip", bytes(b)
    if kind == "truncate":
        return "truncate", data[:rng.randrange(len(data))]
    if kind == "splice":
        o = rng.choice(others)
        return "splice", data[:rng.randrange(len(data))] + o[rng.randrange(len(o)):]
    try:
        zin = zipfile.ZipFile(io.BytesIO(data))
        names = [n for n in zin.namelist() if n.endswith((".xml", ".rels"))]
        victim = rng.choice(names)
        out = io.BytesIO()
        with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
            k = "xml"
            for n in zin.namelist():
                d = zin.read(n)
                if n == victim:
                    k, t = mutate_xml(rng, d.decode("utf-8", errors="replace"))
                    d = t.encode("utf-8", errors="surrogatepass")
                z.writestr(n, d)
        return "xml-" + k, out.getvalue()
    except Exception:
        return "flip", data[: len(data) // 2]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("seeds")
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--bin", default=".lake/build/bin/xlsxlean")
    ap.add_argument("--timeout", type=float, default=20)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    seeds = [os.path.join(a.seeds, f) for f in sorted(os.listdir(a.seeds)) if f.endswith(".xlsx")]
    blobs = [open(f, "rb").read() for f in seeds]
    os.makedirs("out/fuzz/failures", exist_ok=True)
    tmp = "out/fuzz/case.xlsx"
    tally, failures = {}, []
    agree = 0
    for i in range(a.n):
        kind, data = mutate(rng, rng.choice(blobs), blobs)
        open(tmp, "wb").write(data)
        try:
            p = subprocess.run([a.bin, "check", "--json", tmp], capture_output=True, timeout=a.timeout)
            ok = p.returncode in (0, 1)
            why = "" if ok else f"exit {p.returncode}: {p.stderr.decode(errors='replace')[-200:]}"
            if ok:
                try:
                    r = json.loads(p.stdout)[0]
                    if "package_check" in r:
                        agree += 1
                        # the report of where lists a reading-rule problem exactly when a proved checker says no
                        listed = [q for q in r["problems"] if q["rule"] not in ("NoOrphans", "DimensionsTight")]
                        checkers = r["package_check"] and r["conforms_check"] and r["workbook_check"]
                        if bool(listed) == checkers:
                            ok, why = False, f"report lists {len(listed)} problems but the checkers say {checkers}"
                            agree -= 1
                except Exception as e:
                    ok, why = False, f"not JSON: {e}"
        except subprocess.TimeoutExpired:
            ok, why = False, f"no answer in {a.timeout} s"
        t = tally.setdefault(kind, [0, 0])
        t[0] += 1
        if not ok:
            t[1] += 1
            path = f"out/fuzz/failures/{i:05d}-{kind}.xlsx"
            open(path, "wb").write(data)
            failures.append((path, why))
    print(f"{a.n} broken files, {len(failures)} failures; the report agreed with the proved checkers on all {agree} that could be read")
    for k, (n, bad) in sorted(tally.items()):
        print(f"  {k:16} {n:5} tried, {bad} failed")
    for path, why in failures[:15]:
        print(f"  FAIL {path}: {why}")
    sys.exit(1 if failures else 0)

if __name__ == "__main__":
    main()
