import Xlsx.Build

/-!
# The XML of each part

Everything here renders what the model already says; nothing is decided at this layer.
`[Content_Types].xml` and the `.rels` parts are written from the `Package`, so they say
exactly what `Workbook.toPackage_wellFormed` is about. The workbook, sheet, style and
shared string parts are written from the `Workbook`.
-/

namespace Xlsx

/-- Escape text for element content. A CR is written as a character reference: XML
parsers turn a literal CR or CR LF into LF, so `a\r\nb` would come back as `a\nb`
(the adversarial corpus caught this with openpyxl). -/
def xmlEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | '\r' => acc ++ "&#13;"
    | c => acc.push c) ""

/-- Escape text for an attribute value, where XML also turns tab and LF into spaces. -/
def attrEscape (s : String) : String :=
  (xmlEscape s).foldl (fun acc c =>
    match c with
    | '\t' => acc ++ "&#9;"
    | '\n' => acc ++ "&#10;"
    | c => acc.push c) ""

def xmlHeader : String := "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n"

namespace PartName

/-- The name relative to a folder, as a relationship target writes it. -/
def renderRelative (p : PartName) : String :=
  String.join (p.dir.map (· ++ "/")) ++ p.stem ++ String.join (p.exts.map ("." ++ ·))

/-- The name of the ZIP entry: the part name without its leading slash. -/
def entryName (p : PartName) : String := p.renderRelative

end PartName

def Package.contentTypesXml (p : Package) : String :=
  xmlHeader
  ++ "<Types xmlns=\"http://schemas.openxmlformats.org/package/2006/content-types\">"
  ++ String.join (p.defaults.map fun (e, t) =>
      s!"<Default Extension=\"{xmlEscape e}\" ContentType=\"{xmlEscape t}\"/>")
  ++ String.join (p.overrides.map fun (n, t) =>
      s!"<Override PartName=\"{xmlEscape n.render}\" ContentType=\"{xmlEscape t}\"/>")
  ++ "</Types>"

def relsXml (rs : List Rel) : String :=
  xmlHeader
  ++ "<Relationships xmlns=\"http://schemas.openxmlformats.org/package/2006/relationships\">"
  ++ String.join (rs.map fun r =>
      if r.external then
        s!"<Relationship Id=\"{attrEscape r.id}\" Type=\"{attrEscape r.type.uri}\" Target=\"{attrEscape r.target.stem}\" TargetMode=\"External\"/>"
      else
        s!"<Relationship Id=\"{attrEscape r.id}\" Type=\"{attrEscape r.type.uri}\" Target=\"{attrEscape (if r.absolute then r.target.render else r.target.renderRelative)}\"/>")
  ++ "</Relationships>"

def mainNs : String := "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
def relNs : String := "http://schemas.openxmlformats.org/officeDocument/2006/relationships"

def Workbook.workbookXml (wb : Workbook) : String :=
  xmlHeader ++ s!"<workbook xmlns=\"{mainNs}\" xmlns:r=\"{relNs}\">"
  ++ (if wb.date1904 then "<workbookPr date1904=\"1\"/>" else "") ++ "<sheets>"
  ++ String.join ((sheetNums wb.sheets.length).zip wb.sheets |>.map fun (i, s) =>
      let st := match s.state with
        | .visible => "" | .hidden => " state=\"hidden\"" | .veryHidden => " state=\"veryHidden\""
      s!"<sheet name=\"{attrEscape s.name}\" sheetId=\"{numeral i}\"{st} r:id=\"{rid i}\"/>")
  ++ "</sheets>"
  ++ (if wb.names.isEmpty then "" else
      "<definedNames>" ++ String.join (wb.names.map fun d =>
        let sc := match d.scope with | some i => s!" localSheetId=\"{i}\"" | none => ""
        let hid := if d.hidden then " hidden=\"1\"" else ""
        s!"<definedName name=\"{attrEscape d.name}\"{sc}{hid}>{xmlEscape d.formula}</definedName>") ++ "</definedNames>")
  ++ "</workbook>"

def Cell.xml (c : Cell) : String :=
  let r := c.ref.toA1
  let s := if c.style = 0 then "" else s!" s=\"{numeral c.style}\""
  let f := match c.formula with | some f => s!"<f>{xmlEscape f}</f>" | none => ""
  match c.stored with
  | .number n => s!"<c r=\"{r}\"{s}>{f}<v>{n}</v></c>"
  | .real m e => s!"<c r=\"{r}\"{s}>{f}<v>{m}E{e}</v></c>"
  | .shared i => s!"<c r=\"{r}\"{s} t=\"s\">{f}<v>{i}</v></c>"
  | .bool b => s!"<c r=\"{r}\"{s} t=\"b\">{f}<v>{if b then 1 else 0}</v></c>"
  | .error code => s!"<c r=\"{r}\"{s} t=\"e\">{f}<v>{xmlEscape code}</v></c>"
  | .empty => if f.isEmpty then s!"<c r=\"{r}\"{s}/>" else s!"<c r=\"{r}\"{s}>{f}</c>"
  | .inline t =>
    -- a formula's text result is t="str"; plain text is an inline string
    if f.isEmpty then s!"<c r=\"{r}\"{s} t=\"inlineStr\"><is><t xml:space=\"preserve\">{xmlEscape t}</t></is></c>"
    else s!"<c r=\"{r}\"{s} t=\"str\">{f}<v>{xmlEscape t}</v></c>"

def tableType : String := "application/vnd.openxmlformats-officedocument.spreadsheetml.table+xml"
def tableRelType : String := "http://schemas.openxmlformats.org/officeDocument/2006/relationships/table"
def hyperlinkRelType : String := "http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink"

/-- `/xl/tables/table<k>.xml` -/
def tablePart (k : Nat) : PartName := ⟨["xl", "tables"], "table" ++ numeral k, ["xml"]⟩

def Table.xml (t : Table) (id : Nat) : String :=
  xmlHeader ++ s!"<table xmlns=\"{mainNs}\" id=\"{id}\" name=\"{attrEscape t.name}\" displayName=\"{attrEscape t.name}\" ref=\"{t.range.toA1}\""
  ++ (if t.header then ">" ++ s!"<autoFilter ref=\"{t.range.toA1}\"/>" else " headerRowCount=\"0\">")
  ++ s!"<tableColumns count=\"{t.columns.length}\">"
  ++ String.join ((List.range t.columns.length).zip t.columns |>.map fun (i, c) =>
      s!"<tableColumn id=\"{i + 1}\" name=\"{attrEscape c}\"/>")
  ++ "</tableColumns><tableStyleInfo name=\"TableStyleMedium2\" showRowStripes=\"1\"/></table>"

/-- A sheet's tables are written only by a package that has their relationships
(`Lab.withTables`); `Workbook.toPackage` does not lay tables out yet. -/
def Sheet.xml (s : Sheet) : String :=
  xmlHeader ++ s!"<worksheet xmlns=\"{mainNs}\" xmlns:r=\"{relNs}\">"
  ++ (match s.dimension with | some d => s!"<dimension ref=\"{d.toA1}\"/>" | none => "")
  ++ "<sheetData>"
  ++ String.join (s.rows.map fun r =>
      s!"<row r=\"{numeral r.index}\">" ++ String.join (r.cells.map Cell.xml) ++ "</row>")
  ++ "</sheetData>"
  ++ (if s.merges.isEmpty then "" else
      s!"<mergeCells count=\"{s.merges.length}\">"
      ++ String.join (s.merges.map fun m => s!"<mergeCell ref=\"{m.toA1}\"/>") ++ "</mergeCells>")
  ++ (if s.hyperlinks.isEmpty then "" else
      "<hyperlinks>" ++ String.join (s.hyperlinks.map fun h =>
        let rid := match h.rid with | some i => s!" r:id=\"{attrEscape i}\"" | none => ""
        let loc := match h.location with | some l => s!" location=\"{attrEscape l}\"" | none => ""
        s!"<hyperlink ref=\"{h.ref.toA1}\"{rid}{loc}/>") ++ "</hyperlinks>")
  ++ (if s.tables.isEmpty then "" else
      s!"<tableParts count=\"{s.tables.length}\">"
      ++ String.join ((List.range s.tables.length).map fun j => s!"<tablePart r:id=\"rId{j + 1}\"/>")
      ++ "</tableParts>")
  ++ "</worksheet>"

def Workbook.sstXml (wb : Workbook) : String :=
  xmlHeader ++ s!"<sst xmlns=\"{mainNs}\" count=\"{wb.sst.length}\" uniqueCount=\"{wb.sst.length}\">"
  ++ String.join (wb.sst.map fun t => s!"<si><t xml:space=\"preserve\">{xmlEscape t}</t></si>")
  ++ "</sst>"

/-- `styles.xml`: the custom number formats, and `cellXfs` with exactly
`wb.styleCount` formats, each with its `numFmtId`; style 0 uses the plain font and the
rest bold. -/
def stylesXml (wb : Workbook) : String :=
  let n := max wb.styleCount 1
  let fmt (i : Nat) := wb.formatOf i
  xmlHeader ++ s!"<styleSheet xmlns=\"{mainNs}\">"
  ++ (if wb.numFmts.isEmpty then "" else
      s!"<numFmts count=\"{wb.numFmts.length}\">" ++ String.join (wb.numFmts.map fun (id, code) =>
        s!"<numFmt numFmtId=\"{id}\" formatCode=\"{attrEscape code}\"/>") ++ "</numFmts>")
  ++ "<fonts count=\"2\"><font><sz val=\"11\"/><name val=\"Calibri\"/></font>"
  ++ "<font><b/><sz val=\"11\"/><name val=\"Calibri\"/></font></fonts>"
  ++ "<fills count=\"2\"><fill><patternFill patternType=\"none\"/></fill>"
  ++ "<fill><patternFill patternType=\"gray125\"/></fill></fills>"
  ++ "<borders count=\"1\"><border><left/><right/><top/><bottom/><diagonal/></border></borders>"
  ++ "<cellStyleXfs count=\"1\"><xf numFmtId=\"0\" fontId=\"0\" fillId=\"0\" borderId=\"0\"/></cellStyleXfs>"
  ++ s!"<cellXfs count=\"{n}\">"
  ++ String.join ((List.range n).map fun i =>
      let font := if i == 0 then "0" else "1"
      let apply := (if i == 0 then "" else " applyFont=\"1\"") ++ (if fmt i == 0 then "" else " applyNumberFormat=\"1\"")
      s!"<xf numFmtId=\"{fmt i}\" fontId=\"{font}\" fillId=\"0\" borderId=\"0\" xfId=\"0\"{apply}/>")
  ++ "</cellXfs><cellStyles count=\"1\"><cellStyle name=\"Normal\" xfId=\"0\" builtinId=\"0\"/></cellStyles>"
  ++ "</styleSheet>"

/-- The content of a part, by what the package says it is. A part the workbook has no
content for (possible in a hand-built package) gets an empty element. -/
def partContent (wb : Workbook) (n : PartName) : String :=
  if n = workbookPart then wb.workbookXml
  else if n = stylesPart then stylesXml wb
  else if n = sstPart then wb.sstXml
  else match ((sheetNums wb.sheets.length).zip wb.sheets).find? (fun (i, _) => sheetPart i = n) with
    | some (_, s) => s.xml
    | none =>
      let all := wb.sheets.flatMap (·.tables)
      match ((List.range' 1 all.length).zip all).find? (fun (k, _) => tablePart k = n) with
      | some (k, t) => t.xml k
      | none => xmlHeader ++ "<empty/>"

/-- Every entry of an archive for package `p`, in the order a reader expects: content
types first, then the relationships parts, then the parts. The entries are exactly
`p.allParts` plus `[Content_Types].xml`. -/
def filesOf (p : Package) (wb : Workbook) : List (String × String) :=
  [("[Content_Types].xml", p.contentTypesXml)]
  ++ p.rels.map (fun (s, rs) => (s.relsPart.entryName, relsXml rs))
  ++ p.parts.map (fun n => (n.entryName, partContent wb n))

def Workbook.files (wb : Workbook) : List (String × String) := filesOf wb.toPackage wb

end Xlsx
