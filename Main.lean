import Xlsx
import Lab.Adversarial

open Lean Xlsx Lab

/-- Write the adversarial corpus and its manifest: `xlsxgen lab <dir> [fuzz count]`. -/
def lab (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "out/lab"
  let n := (args.drop 1).head?.bind String.toNat? |>.getD 300
  IO.FS.createDirAll dir
  let cases := broken ++ probes ++ fuzz n
  let mut entries : Array Json := #[]
  for c in cases do
    let files := (filesOf c.pkg c.wb).map fun (name, s) => ({ name, data := s.toUTF8 } : Zip.Entry)
    IO.FS.writeBinFile (dir / s!"{c.name}.xlsx") (Zip.archive files)
    entries := entries.push c.manifest
  IO.FS.writeFile (dir / "manifest.json") (Json.arr entries).compress
  IO.println s!"wrote {cases.length} files to {dir}"
  let wrong := cases.filter fun c => c.accepted != c.expectAccept
  for c in wrong do
    IO.eprintln s!"{c.name}: spec says {if c.accepted then "accept" else "reject"}, expected otherwise"
  IO.println s!"spec verdicts as expected on {cases.length - wrong.length}/{cases.length}"
  return if wrong.isEmpty then 0 else 1

/-- Write the example workbook as a real `.xlsx` file: `xlsxgen [path]`. -/
def example_ (args : List String) : IO UInt32 := do
  let path := args.headD "out/example.xlsx"
  let wb := Example.workbook
  unless wb.check do
    IO.eprintln "the example workbook fails its own checker"
    return 1
  let entries := wb.files.map fun (n, s) => ({ name := n, data := s.toUTF8 } : Zip.Entry)
  if let some dir := System.FilePath.parent path then IO.FS.createDirAll dir
  IO.FS.writeBinFile path (Zip.archive entries)
  IO.println s!"wrote {path}: {entries.length} entries"
  for (n, s) in wb.files do
    IO.println s!"  {n} ({s.utf8ByteSize} bytes)"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | "lab" :: rest => lab rest
  | rest => example_ rest
