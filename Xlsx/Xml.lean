import Xlsx.Build

/-!
# The XML of each part

Everything here renders what the model already says; nothing is decided at this layer.
`[Content_Types].xml` and the `.rels` parts are written from the `Package`, so they say
exactly what `Workbook.toPackage_wellFormed` is about. The workbook, sheet, style and
shared string parts are written from the `Workbook`.
-/

namespace Xlsx

def xmlEscape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
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
      s!"<Relationship Id=\"{xmlEscape r.id}\" Type=\"{r.type.uri}\" Target=\"{xmlEscape r.target.renderRelative}\"/>")
  ++ "</Relationships>"

def mainNs : String := "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
def relNs : String := "http://schemas.openxmlformats.org/officeDocument/2006/relationships"

def Workbook.workbookXml (wb : Workbook) : String :=
  xmlHeader ++ s!"<workbook xmlns=\"{mainNs}\" xmlns:r=\"{relNs}\"><sheets>"
  ++ String.join ((sheetNums wb.sheets.length).zip wb.sheets |>.map fun (i, s) =>
      s!"<sheet name=\"{xmlEscape s.name}\" sheetId=\"{numeral i}\" r:id=\"{rid i}\"/>")
  ++ "</sheets></workbook>"

def Cell.xml (c : Cell) : String :=
  let r := c.ref.toA1
  let s := if c.style = 0 then "" else s!" s=\"{numeral c.style}\""
  match c.stored with
  | .number n => s!"<c r=\"{r}\"{s}><v>{n}</v></c>"
  | .shared i => s!"<c r=\"{r}\"{s} t=\"s\"><v>{i}</v></c>"
  | .bool b => s!"<c r=\"{r}\"{s} t=\"b\"><v>{if b then 1 else 0}</v></c>"
  | .inline t => s!"<c r=\"{r}\"{s} t=\"inlineStr\"><is><t>{xmlEscape t}</t></is></c>"

def Sheet.xml (s : Sheet) : String :=
  xmlHeader ++ s!"<worksheet xmlns=\"{mainNs}\"><sheetData>"
  ++ String.join (s.rows.map fun r =>
      s!"<row r=\"{numeral r.index}\">" ++ String.join (r.cells.map Cell.xml) ++ "</row>")
  ++ "</sheetData></worksheet>"

def Workbook.sstXml (wb : Workbook) : String :=
  xmlHeader ++ s!"<sst xmlns=\"{mainNs}\" count=\"{wb.sst.length}\" uniqueCount=\"{wb.sst.length}\">"
  ++ String.join (wb.sst.map fun t => s!"<si><t xml:space=\"preserve\">{xmlEscape t}</t></si>")
  ++ "</sst>"

/-- Two formats: `0` is the default, `1` is bold. `styleCount` in the model is 2. -/
def stylesXml : String :=
  xmlHeader ++ s!"<styleSheet xmlns=\"{mainNs}\">"
  ++ "<fonts count=\"2\"><font><sz val=\"11\"/><name val=\"Calibri\"/></font>"
  ++ "<font><b/><sz val=\"11\"/><name val=\"Calibri\"/></font></fonts>"
  ++ "<fills count=\"2\"><fill><patternFill patternType=\"none\"/></fill>"
  ++ "<fill><patternFill patternType=\"gray125\"/></fill></fills>"
  ++ "<borders count=\"1\"><border><left/><right/><top/><bottom/><diagonal/></border></borders>"
  ++ "<cellStyleXfs count=\"1\"><xf numFmtId=\"0\" fontId=\"0\" fillId=\"0\" borderId=\"0\"/></cellStyleXfs>"
  ++ "<cellXfs count=\"2\"><xf numFmtId=\"0\" fontId=\"0\" fillId=\"0\" borderId=\"0\" xfId=\"0\"/>"
  ++ "<xf numFmtId=\"0\" fontId=\"1\" fillId=\"0\" borderId=\"0\" xfId=\"0\" applyFont=\"1\"/></cellXfs>"
  ++ "<cellStyles count=\"1\"><cellStyle name=\"Normal\" xfId=\"0\" builtinId=\"0\"/></cellStyles>"
  ++ "</styleSheet>"

/-- Every entry of the archive, in the order a reader expects: content types first. -/
def Workbook.files (wb : Workbook) : List (String × String) :=
  let p := wb.toPackage
  [("[Content_Types].xml", p.contentTypesXml)]
  ++ p.rels.map (fun (s, rs) => (s.relsPart.entryName, relsXml rs))
  ++ [(workbookPart.entryName, wb.workbookXml),
      (stylesPart.entryName, stylesXml),
      (sstPart.entryName, wb.sstXml)]
  ++ ((sheetNums wb.sheets.length).zip wb.sheets).map (fun (i, s) => ((sheetPart i).entryName, s.xml))

end Xlsx
