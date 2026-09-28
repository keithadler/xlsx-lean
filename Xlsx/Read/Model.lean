import Xlsx.Xml
import Xlsx.Read.Xml
import Xlsx.Read.Zip

/-!
# From a real file to the model

`load` turns the entries of an `.xlsx` into a `Package` and a `Workbook`, the same
types the theorems are about, so the proved checkers can judge any file.

Nothing is dropped silently. What the reader cannot place in the model goes into
`notes`: `error` notes are problems the reader itself found (a sheet whose `r:id` names
no relationship, a value that is not a number), `unmodeled` notes are content the model
does not describe yet (merged cells, drawings, dates), and `info` notes say how
something was read.

This is runtime code; nothing about it is proved. What is proved is what the checkers
conclude about the model it builds.
-/

namespace Xlsx.Read

inductive Severity where
  | error | unmodeled | info
  deriving DecidableEq, Repr

structure Note where
  severity : Severity
  place : String
  text : String

structure Loaded where
  pkg : Package
  wb : Workbook
  /-- The worksheets, as `(sheet name, entry name)`. -/
  sheetEntries : Array (String × String)
  notes : Array Note
  entries : Nat

/-! ## Names and paths -/

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Undo `%XX` escapes (part names and targets are IRIs). -/
def percentDecode (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : ByteArray := ByteArray.empty
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '%' && i + 2 < cs.size then
      match hexVal cs[i+1]!, hexVal cs[i+2]! with
      | some a, some b => out := out.push (a * 16 + b).toUInt8; i := i + 3; continue
      | _, _ => pure ()
    out := out ++ (String.singleton c).toUTF8
    i := i + 1
  return (String.fromUTF8? out).getD s

/-- A part name from a path without its leading slash: `xl/worksheets/sheet1.xml`. -/
def partOfPath (path : String) : PartName :=
  let segs := path.splitOn "/"
  let file := segs.getLast!
  match file.splitOn "." with
  | stem :: exts => ⟨segs.dropLast, stem, exts⟩
  | [] => ⟨segs.dropLast, file, []⟩

/-- `..` and `.` removed; `none` if it climbs above the root. -/
def normalize (segs : List String) : Option (List String) :=
  segs.foldl (fun acc s => acc.bind fun a =>
    if s == "." || s == "" then some a
    else if s == ".." then (if a.isEmpty then none else some a.dropLast)
    else some (a ++ [s])) (some [])

/-- A relationship target, relative when the file wrote it plainly, absolute otherwise. -/
def targetOf (srcDir : List String) (raw : String) : Option (PartName × Bool) :=
  let t := percentDecode raw
  if t.startsWith "/" then
    (normalize ((t.drop 1).toString.splitOn "/")).map fun segs => (partOfPath ("/".intercalate segs), true)
  else
    let segs := t.splitOn "/"
    if segs.any (fun s => s == ".." || s == ".") then
      (normalize (srcDir ++ segs)).map fun segs => (partOfPath ("/".intercalate segs), true)
    else some (partOfPath t, false)

/-- The source whose relationships a `.rels` entry holds, if it is one. -/
def relsSource (path : String) : Option Source :=
  if path == "_rels/.rels" then some .package
  else
    let segs := path.splitOn "/"
    match segs.reverse with
    | file :: "_rels" :: dirRev =>
      if file.endsWith ".rels" && file != ".rels" then
        let srcFile := (file.dropEnd 5).toString
        some (.part (partOfPath ("/".intercalate (dirRev.reverse ++ [srcFile]))))
      else none
    | _ => none

def relTypeOf (uri : String) : RelType :=
  let tail := (uri.splitOn "/").getLast!
  let known : List (String × RelType) :=
    [("officeDocument", .officeDocument), ("core-properties", .coreProperties),
     ("extended-properties", .extendedProperties), ("worksheet", .worksheet),
     ("sharedStrings", .sharedStrings), ("styles", .styles), ("theme", .theme)]
  let base := ["http://schemas.openxmlformats.org/officeDocument/2006/relationships/",
               "http://schemas.openxmlformats.org/package/2006/relationships/metadata/",
               "http://purl.oclc.org/ooxml/officeDocument/relationships/",
               "http://schemas.openxmlformats.org/package/2006/relationships/metadata/"]
  match known.lookup tail with
  | some t => if base.any (fun b => uri == b ++ tail) then t else .other uri
  | none => .other uri

/-! ## Values -/

/-- `"3.25"` is `real 325 (-2)`, `"1E-3"` is `real 1 (-3)`, `"42"` is `number 42`. -/
def parseNumber (s : String) : Option Stored := Id.run do
  let cs := s.trimAscii.toString.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let intDigits := cs.takeWhile Char.isDigit
  let cs := cs.drop intDigits.length
  let (fracDigits, cs) := match cs with
    | '.' :: r => let d := r.takeWhile Char.isDigit; (d, r.drop d.length)
    | r => ([], r)
  if intDigits.isEmpty && fracDigits.isEmpty then return none
  let (exp, cs, hasExp) : Int × List Char × Bool := match cs with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (eneg, r) := match r with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
        let d := r.takeWhile Char.isDigit
        if d.isEmpty then (0, e :: r, false)
        else
          let v : Int := (String.ofList d).toNat!
          (if eneg then -v else v, r.drop d.length, true)
      else (0, e :: r, false)
    | [] => (0, [], false)
  unless cs.isEmpty do return none
  let m : Int := (String.ofList (intDigits ++ fracDigits)).toNat!
  let m := if neg then -m else m
  if fracDigits.isEmpty && !hasExp then return some (.number m)
  return some (.real m (exp - fracDigits.length))

/-- Text of `<si>` or `<is>`: the `<t>` directly inside and the `<t>` of each run, not
the phonetic guide. -/
def richText (n : Node) : String :=
  n.children.foldl (fun acc k =>
    match k.name with
    | "t" => acc ++ k.textContent
    | "r" => acc ++ ((k.child? "t").map Node.textContent).getD ""
    | _ => acc) ""

/-! ## Loading -/

def worksheetKnown : List String :=
  ["sheetPr", "dimension", "sheetViews", "sheetFormatPr", "cols", "sheetData", "pageMargins",
   "pageSetup", "headerFooter", "printOptions", "sheetCalcPr", "extLst", "mergeCells", "tableParts"]

def parsePart (notes : Array Note) (name : String) (data : ByteArray) : Option Node × Array Note :=
  match parse data with
  | .ok n => (some n, notes)
  | .error e => (none, notes.push ⟨.error, name, e⟩)

def loadSheet (sheetName : String) (entry : String) (root : Node) (notes : Array Note) :
    Sheet × Array Note := Id.run do
  let mut notes := notes
  let place := s!"{sheetName} ({entry})"
  let extra := root.children.filter (fun k => !worksheetKnown.contains k.name) |>.map (·.name)
  unless extra.isEmpty do
    notes := notes.push ⟨.unmodeled, place, ", ".intercalate extra.toList⟩
  let mut rows : Array Row := #[]
  let mut prevRow := 0
  let some data := root.child? "sheetData" | return ({ name := sheetName, rows := [] }, notes)
  let mut shared := 0
  let mut dates := 0
  for rn in data.childrenNamed "row" do
    let idx := match rn.attr? "r" with
      | some r => r.toNat?.getD 0
      | none => prevRow + 1
    prevRow := idx
    let mut cells : Array Cell := #[]
    let mut prevCol := 0
    for cn in rn.childrenNamed "c" do
      let ref : Option CellRef := match cn.attr? "r" with
        | some r => parseA1 r
        | none => some ⟨prevCol + 1, idx⟩
      let some ref := ref
        | notes := notes.push ⟨.error, place, s!"row {idx}: cell reference {(cn.attr? "r").getD ""} is not A1 form"⟩
      prevCol := ref.col
      let style := ((cn.attr? "s").bind String.toNat?).getD 0
      let formula := (cn.child? "f").map Node.textContent
      if let some f := cn.child? "f" then
        if f.attr? "t" == some "shared" then shared := shared + 1
      -- an empty <v/> is a formula with no cached value yet (openpyxl writes these)
      let v := ((cn.child? "v").map Node.textContent).filter (!·.trimAscii.isEmpty)
      let t := (cn.attr? "t").getD "n"
      let a1 := ref.toA1
      let stored : Stored ← match t, v with
        | "s", some v => match v.trimAscii.toString.toNat? with
          | some i => pure (.shared i)
          | none => do notes := notes.push ⟨.error, place, s!"{a1}: shared string index {v} is not a number"⟩; pure .empty
        | "b", some v => pure (.bool (v.trimAscii.toString == "1" || v.trimAscii.toString == "true"))
        | "e", some v => pure (.error v)
        | "str", some v => pure (.inline v)
        | "inlineStr", _ => pure (.inline (((cn.child? "is").map richText).getD ""))
        | "d", some v => do dates := dates + 1; pure (.inline v)
        | "n", some v => match parseNumber v with
          | some s => pure s
          | none => do notes := notes.push ⟨.error, place, s!"{a1}: {v} is not a number"⟩; pure .empty
        | "n", none | "s", none | "b", none | "e", none | "str", none | "d", none => pure .empty
        | other, _ => do notes := notes.push ⟨.error, place, s!"{a1}: unknown cell type t=\"{other}\""⟩; pure .empty
      cells := cells.push (Cell.mk ref stored style formula)
    rows := rows.push ⟨idx, cells.toList⟩
  let mut dimension : Option Range := none
  if let some d := root.child? "dimension" then
    match (d.attr? "ref").bind parseRange with
    | some r => dimension := some r
    | none => notes := notes.push ⟨.error, place, s!"dimension ref {(d.attr? "ref").getD ""} is not a range"⟩
  let mut merges : List Range := []
  if let some mc := root.child? "mergeCells" then
    for m in mc.childrenNamed "mergeCell" do
      match (m.attr? "ref").bind parseRange with
      | some r => merges := merges ++ [r]
      | none => notes := notes.push ⟨.error, place, s!"mergeCell ref {(m.attr? "ref").getD ""} is not a range"⟩
  if shared > 0 then
    notes := notes.push ⟨.unmodeled, place, s!"{shared} shared formulas (kept as written, not expanded)"⟩
  if dates > 0 then
    notes := notes.push ⟨.unmodeled, place, s!"{dates} ISO date cells (t=\"d\"), read as text"⟩
  return ({ name := sheetName, rows := rows.toList, dimension, merges }, notes)

def load (entries : Array ZipEntry) : Loaded := Id.run do
  let mut notes : Array Note := #[]
  let mut parts : List PartName := []
  let mut rels : List (Source × List Rel) := []
  let mut defaults : List (String × String) := []
  let mut overrides : List (PartName × String) := []
  let mut sawTypes := false
  let files : List (String × ByteArray) :=
    (entries.filter (fun e => !e.name.endsWith "/")).toList.map fun e => (e.name, e.data)
  for (name, data) in files do
    if name == "[Content_Types].xml" then
      sawTypes := true
      let (root, n) := parsePart notes name data
      notes := n
      if let some root := root then
        for d in root.childrenNamed "Default" do
          defaults := defaults ++ [((d.attr? "Extension").getD "", (d.attr? "ContentType").getD "")]
        for o in root.childrenNamed "Override" do
          let pn := percentDecode ((o.attr? "PartName").getD "")
          overrides := overrides ++ [(partOfPath ((pn.dropWhile (· == '/')).toString), (o.attr? "ContentType").getD "")]
    else match relsSource name with
      | some src =>
        let (root, n) := parsePart notes name data
        notes := n
        let mut rs : List Rel := []
        if let some root := root then
          for r in root.childrenNamed "Relationship" do
            let id := (r.attr? "Id").getD ""
            if r.attr? "TargetMode" == some "External" then
              notes := notes.push ⟨.info, name, s!"{id}: external target, not a part"⟩
              continue
            match targetOf src.dir ((r.attr? "Target").getD "") with
            | some (target, absolute) =>
              rs := rs ++ [{ id, type := relTypeOf ((r.attr? "Type").getD ""), target, absolute }]
            | none => notes := notes.push ⟨.error, name, s!"{id}: target {(r.attr? "Target").getD ""} climbs out of the package"⟩
        rels := rels ++ [(src, rs)]
      | none =>
        if name.contains '\\' then
          notes := notes.push ⟨.error, name, "a backslash in an entry name; ZIP and OPC separate folders with /"⟩
        parts := parts ++ [partOfPath name]
  unless sawTypes do notes := notes.push ⟨.error, "[Content_Types].xml", "missing"⟩
  let pkg : Package := { parts, defaults, overrides, rels }
  -- part names are compared without ASCII case, as OPC requires
  let data (p : PartName) : Option ByteArray :=
    (files.find? (fun (n, _) => (partOfPath n).key == p.key)).map (·.2)
  -- The workbook, found the way a reader finds it.
  let mut sheets : List Sheet := []
  let mut sheetEntries : Array (String × String) := #[]
  let mut sst : List String := []
  let mut styleCount := 1
  let mut numFmts : List (Nat × String) := []
  let mut xfFormats : List Nat := []
  let mut date1904 := false
  let mut names : List DefinedName := []
  match pkg.mainDocument with
  | [main] =>
    let mainRels := pkg.relsOf (.part main)
    let find (t : RelType) := mainRels.find? (·.type == t)
    if let some r := find .sharedStrings then
      if let some d := data (r.resolve main.dir) then
        let (root, n) := parsePart notes (r.resolve main.dir).entryName d
        notes := n
        if let some root := root then sst := (root.childrenNamed "si").toList.map richText
    if let some r := find .styles then
      if let some d := data (r.resolve main.dir) then
        let (root, n) := parsePart notes (r.resolve main.dir).entryName d
        notes := n
        if let some root := root then
          styleCount := ((root.child? "cellXfs").map (·.childrenNamed "xf" |>.size)).getD 1
          numFmts := (((root.child? "numFmts").map (·.childrenNamed "numFmt")).getD #[]).toList.map fun f =>
            (((f.attr? "numFmtId").bind String.toNat?).getD 0, (f.attr? "formatCode").getD "")
          xfFormats := (((root.child? "cellXfs").map (·.childrenNamed "xf")).getD #[]).toList.map fun x =>
            ((x.attr? "numFmtId").bind String.toNat?).getD 0
          if xfFormats.all (· == 0) then xfFormats := []
    match data main with
    | none => notes := notes.push ⟨.error, main.render, "the main document is not in the archive"⟩
    | some d =>
      let (root, n) := parsePart notes main.entryName d
      notes := n
      if let some root := root then
        for d in ((root.child? "definedNames").map (·.childrenNamed "definedName")).getD #[] do
          let scope := (d.attr? "localSheetId").bind String.toNat?
          let hidden := d.attr? "hidden" == some "1" || d.attr? "hidden" == some "true"
          names := names ++ [DefinedName.mk ((d.attr? "name").getD "") scope d.textContent hidden]
        if let some pr := root.child? "workbookPr" then
          date1904 := pr.attr? "date1904" == some "1" || pr.attr? "date1904" == some "true"
        for s in ((root.child? "sheets").map (·.childrenNamed "sheet")).getD #[] do
          let sname := (s.attr? "name").getD ""
          let rid := (s.attr? "id").getD ""
          match mainRels.find? (·.id == rid) with
          | none => notes := notes.push ⟨.error, main.entryName, s!"sheet {sname}: r:id {rid} names no relationship"⟩
          | some r =>
            if r.type != .worksheet then
              notes := notes.push ⟨.unmodeled, main.entryName, s!"sheet {sname}: a {RelType.uri r.type |>.splitOn "/" |>.getLast!}, not a worksheet"⟩
            else
              let target := r.resolve main.dir
              match data target with
              | none => pure ()  -- the package check reports the dangling target
              | some d =>
                let (root, n) := parsePart notes target.entryName d
                notes := n
                if let some root := root then
                  let (sheet, n) := loadSheet sname target.entryName root notes
                  notes := n
                  let state : SheetState := match s.attr? "state" with
                    | some "hidden" => .hidden | some "veryHidden" => .veryHidden | _ => .visible
                  -- tables: <tablePart r:id> through the sheet's own relationships
                  let mut tables : List Table := []
                  let sheetRels := pkg.relsOf (.part target)
                  for tp in ((root.child? "tableParts").map (·.childrenNamed "tablePart")).getD #[] do
                    let tid := (tp.attr? "id").getD ""
                    match sheetRels.find? (·.id == tid) with
                    | none => notes := notes.push ⟨.error, target.entryName, s!"tablePart {tid} names no relationship"⟩
                    | some tr =>
                      match data (tr.resolve target.dir) with
                      | none => pure ()
                      | some tb =>
                        let (troot, n) := parsePart notes (tr.resolve target.dir).entryName tb
                        notes := n
                        if let some troot := troot then
                          match (troot.attr? "ref").bind parseRange with
                          | none => notes := notes.push ⟨.error, (tr.resolve target.dir).entryName, "the table's ref is not a range"⟩
                          | some range =>
                            let tname := (troot.attr? "displayName").getD ((troot.attr? "name").getD "")
                            let header := troot.attr? "headerRowCount" != some "0"
                            let cols := (((troot.child? "tableColumns").map (·.childrenNamed "tableColumn")).getD #[]).toList.map
                              fun c => (c.attr? "name").getD ""
                            tables := tables ++ [Table.mk tname range header cols]
                  sheets := sheets ++ [{ sheet with state, tables }]
                  sheetEntries := sheetEntries.push (sname, target.entryName)
  | [] => notes := notes.push ⟨.error, "_rels/.rels", "no officeDocument relationship"⟩
  | _ => notes := notes.push ⟨.error, "_rels/.rels", "more than one officeDocument relationship"⟩
  let modeled := [workbookType, worksheetType, stylesType, sstType, relsType,
    "application/vnd.openxmlformats-officedocument.spreadsheetml.table+xml"]
  let others := pkg.parts.filter fun p => !(modeled.contains ((pkg.contentType p).getD ""))
  unless others.isEmpty do
    notes := notes.push ⟨.unmodeled, "package", s!"{others.length} parts outside the model: " ++
      ", ".intercalate (others.take 8 |>.map (·.entryName)) ++ (if others.length > 8 then ", …" else "")⟩
  let wb : Workbook := { sheets, sst, styleCount, numFmts, xfFormats, date1904, names }
  return { pkg := pkg, wb := wb, sheetEntries := sheetEntries, notes := notes, entries := entries.size }

def loadFile (path : System.FilePath) : IO (Except String Loaded) := do
  let bytes ← IO.FS.readBinFile path
  return (readZip bytes).map load

end Xlsx.Read
