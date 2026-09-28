"""Summarize `xlsxgen check --json` output, and optionally insist on the numbers.

    xlsxgen check --json tests/*.xlsx > checks.json
    python tools/summarize_checks.py checks.json --expect-files 66 --expect-unreadable 2 --expect-pass 62
"""
import argparse, collections, json, os, sys

ap = argparse.ArgumentParser()
ap.add_argument("json")
ap.add_argument("--expect-files", type=int)
ap.add_argument("--expect-unreadable", type=int)
ap.add_argument("--expect-pass", type=int)
a = ap.parse_args()

d = json.load(open(a.json))
unreadable = [x for x in d if "unreadable" in x]
readable = [x for x in d if "unreadable" not in x]
def passes(x):
    return x["package_check"] and x["conforms_check"] and x["workbook_check"] and x["reader_errors"] == 0
ok = [x for x in readable if passes(x)]
print(f"{len(d)} files, {len(unreadable)} unreadable, {len(ok)} of {len(readable)} follow the spec")
for x in unreadable:
    print(f"  unreadable  {os.path.basename(x['path'])}: {x['unreadable'][:100]}")
for x in readable:
    if not passes(x):
        rules = collections.Counter(p["rule"] for p in x["problems"] if p["rule"] != "NoOrphans")
        errs = [n["text"] for n in x["notes"] if n["severity"] == "error"]
        print(f"  breaks      {os.path.basename(x['path'])}: {dict(rules)} {errs[:1]}")
bad = False
for name, want, got in [("files", a.expect_files, len(d)), ("unreadable", a.expect_unreadable, len(unreadable)),
                        ("pass", a.expect_pass, len(ok))]:
    if want is not None and want != got:
        print(f"expected {want} {name}, got {got}")
        bad = True
sys.exit(1 if bad else 0)
