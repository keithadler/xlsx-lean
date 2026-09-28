import Xlsx
import Lab.Adversarial
import Xlsx.Read.Report

open Lean Xlsx Lab

/-- Write the adversarial corpus and its manifest: `xlsxgen lab <dir> [fuzz count]`. -/
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

/-- Write the example workbook as a real `.xlsx` file: `xlsxgen [path]`. -/
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

/-- Check real files: `xlsxgen check [--json] file.xlsx ...`. Exit 1 if any breaks the spec. -/
def check (args : List String) : IO UInt32 := do
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

def main (args : List String) : IO UInt32 :=
  match args with
  | "lab" :: rest => lab rest
  | "check" :: rest => check rest
  | rest => example_ rest
