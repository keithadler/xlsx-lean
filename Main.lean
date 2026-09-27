import Xlsx

open Xlsx

/-- Write the example workbook as a real `.xlsx` file. -/
def main (args : List String) : IO UInt32 := do
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
