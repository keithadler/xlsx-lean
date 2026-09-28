import Lean
import Xlsx.Example

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

/-! ## Data for the widgets -/

def RelType.short : RelType → String
  | .officeDocument => "officeDocument"
  | .coreProperties => "core-properties"
  | .extendedProperties => "extended-properties"
  | .worksheet => "worksheet"
  | .sharedStrings => "sharedStrings"
  | .styles => "styles"
  | .theme => "theme"
  | .other u => (u.splitOn "/").getLast!

def role (contentType : Option String) : String :=
  match contentType with
  | some t =>
    if t == relsType then "rels"
    else if t == workbookType then "workbook"
    else if t == worksheetType then "worksheet"
    else if t == stylesType then "styles"
    else if t == sstType then "sharedStrings"
    else "other"
  | none => "untyped"

def sourceJson : Source → Json
  | .package => "package"
  | .part p => p.entryName

def packageJson (p : Package) (title : String) (sheets : Nat) : Json :=
  let parts := p.allParts.map fun n =>
    let ct := p.contentType n
    let via := if (p.overrides.lookup n).isSome then "Override" else
      if ct.isSome then s!"Default .{n.ext}" else "none"
    Json.mkObj [("entry", n.entryName), ("partName", n.render), ("ext", n.ext),
      ("contentType", match ct with | some t => Json.str t | none => Json.null),
      ("via", via), ("role", role ct)]
  let rels := p.rels.map fun (s, rs) =>
    Json.mkObj [("source", sourceJson s), ("relsPart", s.relsPart.entryName),
      ("items", Json.arr (rs.map fun r => Json.mkObj [("id", r.id),
        ("type", RelType.short r.type), ("target", (r.resolve s.dir).entryName),
        ("written", r.target.renderRelative)]).toArray)]
  Json.mkObj [("title", title), ("parts", Json.arr parts.toArray), ("rels", Json.arr rels.toArray),
    ("defaults", Json.arr (p.defaults.map fun (e, t) => Json.mkObj [("ext", e), ("type", t)]).toArray),
    ("check", toJson p.check), ("conforms", toJson (conformsCheck p sheets)),
    ("orphans", toJson p.orphanCheck)]

def cellJson (sst : List String) (c : Cell) : Json :=
  let (kind, raw) := match c.stored with
    | .number n => ("number", toString n)
    | .shared i => ("shared", toString i)
    | .bool b => ("bool", if b then "1" else "0")
    | .inline s => ("inline", s)
    | .real m e => ("real", s!"{m}E{e}")
    | .error c => ("error", c)
    | .empty => ("empty", "")
  let value : Json := match c.stored.resolve sst with
    | some (.number n) => Json.mkObj [("kind", "number"), ("text", toString n)]
    | some (.text s) => Json.mkObj [("kind", "text"), ("text", s)]
    | some (.bool b) => Json.mkObj [("kind", "bool"), ("text", if b then "TRUE" else "FALSE")]
    | some (.real m e) => Json.mkObj [("kind", "number"), ("text", s!"{m}E{e}")]
    | some (.error c) => Json.mkObj [("kind", "error"), ("text", c)]
    | some .empty => Json.mkObj [("kind", "empty"), ("text", "")]
    | none => Json.mkObj [("kind", "missing"), ("text", "#REF!")]
  Json.mkObj [("ref", c.ref.toA1), ("col", toJson c.ref.col), ("row", toJson c.ref.row), ("kind", kind),
    ("raw", raw), ("value", value), ("style", toJson c.style), ("xml", c.xml)]

def workbookJson (wb : Workbook) : Json :=
  let sheets := ((sheetNums wb.sheets.length).zip wb.sheets).map fun (i, s) =>
    let maxc := (s.rows.flatMap (·.cells.map (·.ref.col))).foldl max 0
    let maxr := (s.rows.map (·.index)).foldl max 0
    Json.mkObj [("name", s.name), ("entry", (sheetPart i).entryName),
      ("ok", toJson (Sheet.check wb s)),
      ("cols", Json.arr ((List.range' 1 (maxc + 1)).map fun c => Json.str (colName c)).toArray),
      ("rows", toJson (maxr + 1)),
      ("dimension", match s.dimension with | some d => Json.str d.toA1 | none => Json.null),
      ("merges", Json.arr (s.merges.toArray.map fun m => Json.mkObj [("ref", m.toA1),
        ("c1", toJson m.first.col), ("r1", toJson m.first.row), ("c2", toJson m.last.col), ("r2", toJson m.last.row)])),
      ("cells", Json.arr (s.rows.flatMap fun r => r.cells.map (cellJson wb.sst)).toArray)]
  Json.mkObj [("sheets", Json.arr sheets.toArray),
    ("sst", Json.arr (wb.sst.map Json.str).toArray), ("check", toJson wb.check)]

/-- The steps `colName` takes on `n`, for the column explorer. -/
def colSteps : Nat → Nat → List Json
  | 0, _ => []
  | _, 0 => []
  | k + 1, m + 1 =>
    Json.mkObj [("n", toJson (m + 1)), ("q", toJson (m / 26)), ("r", toJson (m % 26)),
      ("letter", toString (letter ⟨m % 26, Nat.mod_lt _ (by decide)⟩))] :: colSteps k (m / 26)

def colTrace (n : Nat) : Json :=
  let name := colName n
  Json.mkObj [("n", toJson n), ("name", name), ("parsed", match parseCol name with
      | some k => toJson k | none => Json.null),
    ("steps", Json.arr (colSteps (n + 1) n).toArray),
    ("near", Json.arr ((List.range' (n - min n 3) 7).filter (fun k => 0 < k) |>.map fun k =>
      Json.mkObj [("n", toJson k), ("name", colName k)]).toArray),
    ("maxCol", toJson maxCol), ("a1", (CellRef.mk n 1).toA1)]

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
  return .pure (packageJson (layout n) s!"layout {n}: a workbook with {n} sheet{if n == 1 then "" else "s"}" n)

/-! ## The widgets -/

@[widget_module]
def PackageMap : Widget.Module where
  javascript := include_str ".." / "widgets" / "package-map.js"

@[widget_module]
def SheetView : Widget.Module where
  javascript := include_str ".." / "widgets" / "sheet-view.js"

@[widget_module]
def ColumnExplorer : Widget.Module where
  javascript := include_str ".." / "widgets" / "column-explorer.js"

end Xlsx.Visuals

open Xlsx Xlsx.Visuals

/-! ## Look at them

Put the cursor on each line. -/

/- The package of the example file: every entry, its content type, every relationship.
The slider lays out a workbook with any number of sheets, asked of Lean live. -/
#widget PackageMap with packageJson Example.workbook.toPackage "example.xlsx" Example.workbook.sheets.length

/- The two sheets as a reader sees them, with the shared strings they point into. -/
#widget SheetView with workbookJson Example.workbook

/- Any column number, named by `colName` and read back by `parseCol`. -/
#widget ColumnExplorer with colTrace 16384
