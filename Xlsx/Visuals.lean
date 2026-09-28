import Lean
import Xlsx.Visuals.Data

/-!
# Pictures of the proofs

Three infoview widgets. Put the cursor on a `#widget` line below, and Lean Studio's
**Infoview** tab (or VS Code's infoview) draws it.

Nothing in the pictures is computed by the JavaScript. The data comes from the same
functions the theorems are about: `toA1` names the cells, `colName` names the columns,
`Stored.resolve` reads the shared strings, `Workbook.toPackage` lays out the parts, and
`Package.check` gives the verdict. The column explorer and the sheet-count slider call
back into Lean over RPC, so what you type is answered by the verified function itself.
-/

open Lean Server

namespace Xlsx.Visuals

/-! ## RPC: the widgets ask Lean -/

structure NatParam where
  n : Nat
  deriving FromJson, ToJson

@[server_rpc_method]
def colTraceRpc (p : NatParam) : RequestM (RequestTask Json) :=
  return .pure (colTrace (min p.n 1000000000))

@[server_rpc_method]
def layoutRpc (p : NatParam) : RequestM (RequestTask Json) :=
  let n := max 1 (min p.n 40)
  return .pure (packageJson (layout n) s!"layout {n}: a workbook with {n} sheet{if n == 1 then "" else "s"}" n true)

/-! ## The widgets -/

@[widget_module]
def PackageMap : Widget.Module where
  javascript := include_str ".." / "widgets" / "package-map.js"

@[widget_module]
def SheetView : Widget.Module where
  javascript := include_str ".." / "widgets" / "sheet-view.js"

@[widget_module]
def CheckReport : Widget.Module where
  javascript := include_str ".." / "widgets" / "check-report.js"

end Xlsx.Visuals

namespace Xlsx.Visuals
open Lean Elab Command

/-- `#xlsx_check "file.xlsx"`: read a real workbook, run the proved checkers on it, and draw
the verdict, the package and the sheets in the infoview. Paths are relative to the project. -/
syntax (name := xlsxCheckCmd) "#xlsx_check " str : command

/-- Run the compiled checker on a file and parse what it says. -/
def runChecker (path : String) : IO (Except String Json) := do
  let exe := "./.lake/build/bin/xlsxlean"
  unless ← System.FilePath.pathExists exe do
    return .error "build the checker first: lake build xlsxlean"
  let out ← IO.Process.output { cmd := exe, args := #["check", "--widget", path] }
  return Json.parse out.stdout

@[command_elab xlsxCheckCmd] def elabXlsxCheck : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  match ← liftIO (runChecker path) with
  | .error e =>
    liftCoreM <| Widget.savePanelWidgetInfo CheckReport.javascriptHash
      (pure (Json.mkObj [("path", path), ("unreadable", e)])) stx
    logWarning m!"{path}: {e}"
  | .ok j =>
    let get (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null
    let report := get "report"
    liftCoreM <| Widget.savePanelWidgetInfo CheckReport.javascriptHash (pure report) stx
    if get "package" != Json.null then
      liftCoreM <| Widget.savePanelWidgetInfo PackageMap.javascriptHash (pure (get "package")) stx
      liftCoreM <| Widget.savePanelWidgetInfo SheetView.javascriptHash (pure (get "workbook")) stx
    match (report.getObjValAs? Bool "ok").toOption with
    | some true => logInfo m!"{path}: follows every rule of the spec"
    | _ => logWarning m!"{path}: breaks the spec, or could not be read"

@[widget_module]
def ColumnExplorer : Widget.Module where
  javascript := include_str ".." / "widgets" / "column-explorer.js"

end Xlsx.Visuals

open Xlsx Xlsx.Visuals

/-! ## Look at them

Put the cursor on each line. -/

/- The package of the example file: every entry, its content type, every relationship.
The slider lays out a workbook with any number of sheets, asked of Lean live. -/
#widget PackageMap with packageJson Example.workbook.toPackage "example.xlsx" Example.workbook.sheets.length true

/- The two sheets as a reader sees them, with the shared strings they point into. -/
#widget SheetView with workbookJson Example.workbook

/- Any column number, named by `colName` and read back by `parseCol`. -/
#widget ColumnExplorer with colTrace 16384

