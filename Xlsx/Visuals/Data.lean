import Lean.Data.Json
import Xlsx.Example
import Xlsx.Read.Report

/-!
# The data the widgets draw

Everything here is computed by the functions the theorems are about. It lives apart from
the widgets so the `xlsxlean` executable can produce it too (`check --widget`), which is
how `#xlsx_check` gets a real file drawn: the compiled reader reads it, and the infoview
draws what it returns.
-/

open Lean

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


/-- What the check report shows about a loaded file. -/
def checkJson (path : String) (l : Read.Loaded) : Json :=
  let v := l.verdict
  let cells := l.wb.sheets.foldl (fun a s => a + s.rows.foldl (fun b r => b + r.cells.length) 0) 0
  match Read.reportJson path l with
  | .obj kvs => .obj ((kvs.insert "summary"
      (Json.str s!"{l.entries} entries · {l.wb.sheets.length} worksheets · {cells} cells · {l.wb.sst.length} shared strings")).insert
      "has_main" (toJson !l.pkg.mainDocument.isEmpty))
  | j => let _ := v; j

/-- The workbook view of a loaded file, at most `cap` cells per sheet so big files stay drawable. -/
def workbookJsonCapped (wb : Workbook) (cap : Nat) : Json :=
  let trim (s : Sheet) : Sheet :=
    let (rows, _) := s.rows.foldl (fun (acc, n) r =>
      if n ≥ cap then (acc, n) else (acc ++ [{ r with cells := r.cells.take (cap - n) }], n + r.cells.length)) ([], 0)
    { s with rows := rows.filter (!·.cells.isEmpty) }
  workbookJson { wb with sheets := wb.sheets.map trim }


end Xlsx.Visuals
