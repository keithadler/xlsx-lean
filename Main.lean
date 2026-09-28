import Xlsx.Zip
import Xlsx.Visuals.Data
import Lab.Adversarial
import Xlsx.Read.Report

open Lean Xlsx Lab

/-- Write the adversarial corpus and its manifest: `xlsxlean lab <dir> [fuzz count]`. -/
def lab (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "out/lab"
  let n := (args.drop 1).head?.bind String.toNat? |>.getD 300
  IO.FS.createDirAll dir
  let cases := broken ++ probes ++ fuzz n
  let mut entries : Array Json := #[]
  let mut roundtrip := 0
  let mut explainAgrees := 0
  let mut mismatches : Array String := #[]
  for c in cases do
    let files := (filesOf c.pkg c.wb).map fun (name, s) => ({ name, data := s.toUTF8 } : Archive.Entry)
    let bytes := Archive.archive files
    IO.FS.writeBinFile (dir / s!"{c.name}.xlsx") bytes
    entries := entries.push c.manifest
    -- read it back with the reader, and compare with the model it was written from
    match Read.readZip bytes with
    | .error e => mismatches := mismatches.push s!"{c.name}: unreadable: {e}"
    | .ok zs =>
      let l := Read.load zs
      let v := l.verdict
      -- the report of where names nothing exactly when the proved checkers say yes
      let clean := v.problems.all (·.rule == "NoOrphans")
      if clean == (v.package && v.conforms && v.workbook) then explainAgrees := explainAgrees + 1
      else mismatches := mismatches.push s!"{c.name}: problems listed {v.problems.size}, checkers say {v.package && v.conforms && v.workbook}"
      if c.accepted then
        let same := l.wb == c.wb && l.pkg.parts == c.pkg.parts && l.pkg.defaults == c.pkg.defaults
          && l.pkg.overrides == c.pkg.overrides && l.pkg.rels == c.pkg.rels
        if same then roundtrip := roundtrip + 1
        else mismatches := mismatches.push s!"{c.name}: read back differently"
  IO.FS.writeFile (dir / "manifest.json") (Json.arr entries).compress
  IO.println s!"wrote {cases.length} files to {dir}"
  let wrong := cases.filter fun c => c.accepted != c.expectAccept
  for c in wrong do
    IO.eprintln s!"{c.name}: spec says {if c.accepted then "accept" else "reject"}, expected otherwise"
  IO.println s!"spec verdicts as expected on {cases.length - wrong.length}/{cases.length}"
  let accepted := (cases.filter (·.accepted)).length
  IO.println s!"read back identical to the model: {roundtrip}/{accepted} accepted files"
  IO.println s!"where-report agrees with the checkers: {explainAgrees}/{cases.length}"
  for m in mismatches.toList.take 20 do IO.eprintln s!"  {m}"
  return if wrong.isEmpty && mismatches.isEmpty then 0 else 1

/-- Write the example workbook as a real `.xlsx` file: `xlsxlean write [path]`. -/
def example_ (args : List String) : IO UInt32 := do
  let path := args.headD "out/example.xlsx"
  let wb := Example.workbook
  unless wb.check do
    IO.eprintln "the example workbook fails its own checker"
    return 1
  let entries := wb.files.map fun (n, s) => ({ name := n, data := s.toUTF8 } : Archive.Entry)
  if let some dir := System.FilePath.parent path then IO.FS.createDirAll dir
  IO.FS.writeBinFile path (Archive.archive entries)
  IO.println s!"wrote {path}: {entries.length} entries"
  for (n, s) in wb.files do
    IO.println s!"  {n} ({s.utf8ByteSize} bytes)"
  return 0

/-- Everything the infoview draws about one file: `xlsxlean check --widget file.xlsx`. -/
def widgetJson (f : String) : IO UInt32 := do
  match ← Read.loadFile f with
  | .error e => IO.println (Json.mkObj [("report", Json.mkObj [("path", f), ("unreadable", e)])]).compress; return 1
  | .ok l =>
    let v := l.verdict
    let ok := v.ok && (l.notes.filter (·.severity == .error)).isEmpty
    let report := match Visuals.checkJson f l with
      | .obj kvs => Json.obj (kvs.insert "ok" (toJson ok))
      | j => j
    IO.println (Json.mkObj [("report", report),
      ("package", Visuals.packageJson l.pkg f l.wb.sheets.length),
      ("workbook", Visuals.workbookJsonCapped l.wb 400 f)]).compress
    return if ok then 0 else 1

/-- A widget module, made to run on a plain page: React from the page, no RPC. -/
def standalone (name src : String) : String :=
  let src := src.replace "import * as React from 'react';" "const React = window.React;"
  let src := src.replace "import { useRpcSession } from '@leanprover/infoview';"
    "const useRpcSession = () => ({ call: () => Promise.reject(new Error('this page is not connected to Lean')) });"
  let src := src.replace "export default function" s!"window.{name} = function"
  s!"<script>(function()\{\n{src}\n})();</script>"

def htmlPage (title : String) (data : Json) : String :=
  let esc (j : Json) := (j.compress.replace "</" "<\\/")
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
  ++ s!"<title>{xmlEscape title}</title>"
  ++ "<style>:root{--vscode-editor-foreground:#1f2328;--bg:#ffffff;color-scheme:light dark}"
  ++ "@media (prefers-color-scheme: dark){:root{--vscode-editor-foreground:#e6e8ee;--bg:#15171c}}"
  ++ "body{margin:0;background:var(--bg);color:var(--vscode-editor-foreground);font-family:system-ui,sans-serif}"
  ++ "main{max-width:1180px;margin:0 auto;padding:24px 16px;display:flex;flex-direction:column;gap:22px}"
  ++ "footer{font-size:12px;opacity:.65;padding:8px 0 24px}</style>"
  ++ "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/react/18.3.1/umd/react.production.min.js\"></script>"
  ++ "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/react-dom/18.3.1/umd/react-dom.production.min.js\"></script>"
  ++ standalone "CheckReport" (include_str "widgets" / "check-report.js")
  ++ standalone "PackageMap" (include_str "widgets" / "package-map.js")
  ++ standalone "SheetView" (include_str "widgets" / "sheet-view.js")
  ++ "</head><body><main><div id=\"report\"></div><div id=\"package\"></div><div id=\"sheets\"></div>"
  ++ "<footer>Made by xlsxlean from github.com/keithadler/xlsx-lean. The verdict comes from checkers proved sound in Lean.</footer></main>"
  ++ s!"<script>const DATA = {esc data};"
  ++ "const h = React.createElement; const mount = (id, C, p) => ReactDOM.createRoot(document.getElementById(id)).render(h(C, p));"
  ++ "mount('report', CheckReport, DATA.report); if (DATA.package) { mount('package', PackageMap, DATA.package); mount('sheets', SheetView, DATA.workbook); }</script>"
  ++ "</body></html>"

/-- One file as a page: `xlsxlean check --html report.html file.xlsx`. -/
def htmlReport (out f : String) : IO UInt32 := do
  let (data, code) ← match ← Read.loadFile f with
    | .error e => pure (Json.mkObj [("report", Json.mkObj [("path", f), ("unreadable", e)])], (1 : UInt32))
    | .ok l =>
      let v := l.verdict
      let ok := v.ok && (l.notes.filter (·.severity == .error)).isEmpty
      let report := match Visuals.checkJson f l with
        | .obj kvs => Json.obj (kvs.insert "ok" (toJson ok))
        | j => j
      pure (Json.mkObj [("report", report), ("package", Visuals.packageJson l.pkg f l.wb.sheets.length),
        ("workbook", Visuals.workbookJsonCapped l.wb 2000 f)], if ok then 0 else 1)
  IO.FS.writeFile out (htmlPage s!"{f}: xlsxlean" data)
  IO.println s!"wrote {out}"
  return code

/-- Check real files: `xlsxlean check [--json] file.xlsx ...`. Exit 1 if any breaks the spec. -/
def check (args : List String) : IO UInt32 := do
  if let ["--widget", f] := args then return ← widgetJson f
  if let ["--html", out, f] := args then return ← htmlReport out f
  let json := args.contains "--json"
  let files := args.filter (· != "--json")
  let mut bad := 0
  let mut out : Array Json := #[]
  for f in files do
    match ← Read.loadFile f with
    | .error e =>
      bad := bad + 1
      if json then out := out.push (Json.mkObj [("path", f), ("unreadable", e)])
      else IO.println s!"{f}\n  ✗ unreadable: {e}\n"
    | .ok l =>
      let v := l.verdict
      unless v.ok && (l.notes.filter (·.severity == .error)).isEmpty do bad := bad + 1
      if json then out := out.push (Read.reportJson f l) else IO.println (Read.reportText f l)
  if json then IO.println (Json.arr out).compress
  return if bad == 0 then 0 else 1

def usage : String := "xlsxlean: the XLSX format as a Lean proof, and a checker for real files.

  xlsxlean check [--json] FILE.xlsx ...   check files against the spec; exit 1 if any breaks it
  xlsxlean check --html OUT.html FILE     the same, as one page to share: verdict, package, sheets
  xlsxlean write [PATH]                   write the example workbook (default out/example.xlsx)
  xlsxlean lab [DIR] [N]                  write the adversarial corpus with N random workbooks
  xlsxlean help                           this

The verdicts come from checkers proved sound in Lean: https://github.com/keithadler/xlsx-lean
"

def main (args : List String) : IO UInt32 :=
  match args with
  | "lab" :: rest => lab rest
  | "check" :: rest => check rest
  | "write" :: rest => example_ rest
  | ["help"] | ["--help"] | ["-h"] | [] => do IO.print usage; return 0
  | other => do IO.eprintln s!"unknown command {other.headD ""}\n"; IO.eprint usage; return 2
