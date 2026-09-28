"""Our verdict next to what each reader does with the same real files.

    xlsxlean check --json DIR/*.xlsx > ours.json
    python tools/compare_verdicts.py ours.json --sheetjs NODE_MODULES [--timeout 120]

For every file: do openpyxl, calamine and SheetJS open it and read every sheet, or do
they refuse (or crash)? The interesting rows are where we and a reader disagree:
a file that follows the spec but a reader refuses, and a file that breaks the spec but
every reader takes without a word.
"""
import argparse, collections, json, os, subprocess, sys, warnings

warnings.filterwarnings("ignore")

def openpyxl_opens(path):
    import openpyxl
    wb = openpyxl.load_workbook(path, data_only=True)
    for ws in wb.worksheets:
        for _ in ws.iter_rows(values_only=True):
            pass

def calamine_opens(path):
    from python_calamine import CalamineWorkbook
    wb = CalamineWorkbook.from_path(path)
    for n in wb.sheet_names:
        wb.get_sheet_by_name(n).to_python()

def attempt_here(f, path):
    try:
        f(path)
        return "opens"
    except KeyboardInterrupt:
        raise
    except BaseException as e:
        return "CRASHES" if type(e).__name__ == "PanicException" else "refuses"

def attempt(name, path, timeout):
    """Each reader opens each file in its own process, so a hang or a runaway is recorded, not waited on."""
    try:
        p = subprocess.run([sys.executable, __file__, "--one", name, path], capture_output=True, text=True, timeout=timeout)
        return p.stdout.strip() or "CRASHES"
    except subprocess.TimeoutExpired:
        return "HANGS"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ours")
    ap.add_argument("--sheetjs")
    ap.add_argument("--timeout", type=float, default=120)
    ap.add_argument("--one")
    a = ap.parse_args()
    if a.one:
        print(attempt_here({"openpyxl": openpyxl_opens, "calamine": calamine_opens}[a.one], a.ours))
        return
    rows = json.load(open(a.ours))
    paths = [r["path"] for r in rows]
    sj = {}
    if a.sheetjs:
        script = ("const X=require('xlsx');for(const p of process.argv.slice(1)){let r='opens';"
                  "try{const w=X.readFile(p);for(const n of w.SheetNames)X.utils.sheet_to_json(w.Sheets[n])}catch(e){r='refuses'}"
                  "console.log(JSON.stringify([p,r]))}")
        for p in paths:
            try:
                out = subprocess.run(["node", "-e", script, p], capture_output=True, text=True, timeout=a.timeout,
                                     env=dict(os.environ, NODE_PATH=a.sheetjs)).stdout
                sj[p] = json.loads(out.splitlines()[-1])[1] if out.strip() else "CRASHES"
            except subprocess.TimeoutExpired:
                sj[p] = "HANGS"
    table = collections.Counter()
    notable = []
    for r in rows:
        p = r["path"]
        if "unreadable" in r:
            ours = "unreadable"
        else:
            ok = r["package_check"] and r["conforms_check"] and r["workbook_check"] and r["reader_errors"] == 0
            ours = "follows" if ok else "breaks"
        o, c = attempt("openpyxl", p, a.timeout), attempt("calamine", p, a.timeout)
        s = sj.get(p, "-")
        table[(ours, o, c, s)] += 1
        if (ours == "follows" and "opens" not in {o} | {c} | {s}) or (ours == "follows" and ("refuses" in (o, c, s) or "CRASHES" in (o, c, s))) \
           or (ours == "breaks" and o == c == s == "opens") or {"CRASHES", "HANGS"} & {o, c, s}:
            notable.append((os.path.basename(p), ours, o, c, s))
    print(f"{'ours':11} {'openpyxl':9} {'calamine':9} {'sheetjs':8} files")
    for (ours, o, c, s), n in sorted(table.items(), key=lambda kv: -kv[1]):
        print(f"{ours:11} {o:9} {c:9} {s:8} {n}")
    print("\nwhere we and a reader part ways:")
    for row in notable:
        print("  " + " | ".join(row))

if __name__ == "__main__":
    main()
