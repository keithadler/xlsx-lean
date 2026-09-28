import Lean.Data.Json
import Xlsx
import Xlsx.Read.Report

/-!
# The adversarial corpus

Three kinds of file, each written by the same writer as the example:

* **broken**: one rule of the spec broken on purpose. Our checkers must say no. The
  question for real readers is whether they notice.
* **probe**: files our checkers *accept*, aimed at the places a spec like this is
  usually too weak: characters XML cannot carry, whitespace, line endings, Excel's own
  limits (string length, sheet names), numbers a double cannot hold.
* **fuzz**: random well-formed workbooks. Every reader should read back exactly the
  values the model says, cell by cell.

For every file the manifest records our verdicts (`Package.check`, `conformsCheck`,
`Workbook.check`) and the value the model gives each cell (`Stored.resolve`), so the
Python side only has to compare.
-/

open Lean Xlsx

namespace Lab

structure Case where
  name : String
  kind : String
  what : String
  wb : Workbook
  pkg : Package

def Case.ofWorkbook (name kind what : String) (wb : Workbook) : Case :=
  { name, kind, what, wb, pkg := wb.toPackage }

def base : Workbook := Example.workbook

/-- Replace the rows of the first sheet. -/
def withRows (rows : List Row) : Workbook :=
  { base with sheets := { Example.limits with rows } :: base.sheets.tail }

def withLimits (f : Sheet → Sheet) : Workbook :=
  { base with sheets := f Example.limits :: base.sheets.tail }

def withSheetName (n : String) : Workbook :=
  { base with sheets := { Example.limits with name := n } :: base.sheets.tail }

def oneCell (c : Cell) (extra : List String := []) : Workbook :=
  { sheets := [{ name := "Probe", rows := [⟨c.ref.row, [c]⟩] }], sst := extra, styleCount := 2 }

def oneCellRow (cs : List Cell) : Workbook :=
  { sheets := [{ name := "Probe", rows := [⟨1, cs⟩] }], sst := [], styleCount := 2 }

def inl (s : String) : Workbook := oneCell ⟨⟨1, 1⟩, .inline s, 0, none⟩
def shd (s : String) : Workbook := oneCell ⟨⟨1, 1⟩, .shared 0, 0, none⟩ [s]
def numw (n : Int) : Workbook := oneCell ⟨⟨1, 1⟩, .number n, 0, none⟩

def lay : Package := layout 2

/-- A case written with `Workbook.toPackage`, which lays out tables, plus each sheet's
hyperlink relationships (external addresses), which the model does not carry. -/
def withTables (name kind what : String) (wb : Workbook) : Case := Id.run do
  let tabled : Workbook := { wb with sheets := wb.sheets.map fun (s : Sheet) =>
    { s with relIds := (List.range' 1 s.tables.length).map rid ++ s.relIds } }
  let base := tabled.toPackage
  let mut rels := base.rels
  let mut parts := base.parts
  let mut overrides := base.overrides
  for (i, s) in (sheetNums wb.sheets.length).zip wb.sheets do
    let links := s.hyperlinks.filterMap (·.rid) |>.filter (s.relIds.contains ·)
    unless links.isEmpty do
      let extra := links.map fun id => Rel.mk id (.other hyperlinkRelType) ⟨[], "https://example.com/" ++ id, []⟩ false true
      if rels.any (·.1 == .part (sheetPart i)) then
        rels := rels.map fun (src, rs) => if src == .part (sheetPart i) then (src, rs ++ extra) else (src, rs)
      else
        rels := rels ++ [(.part (sheetPart i), extra)]
  -- comments: a part per sheet that has any, and a relationship to it
  for (i, s) in (sheetNums wb.sheets.length).zip wb.sheets do
    unless s.comments.isEmpty do
      let r := Rel.mk "rIdC" (.other commentsRelType) (commentsPart i) true false
      parts := parts ++ [commentsPart i]
      overrides := overrides ++ [(commentsPart i, commentsType)]
      if rels.any (·.1 == .part (sheetPart i)) then
        rels := rels.map fun (src, rs) => if src == .part (sheetPart i) then (src, rs ++ [r]) else (src, rs)
      else
        rels := rels ++ [(.part (sheetPart i), [r])]
  let tabled : Workbook := { tabled with sheets := tabled.sheets.map fun (s : Sheet) =>
    if s.comments.isEmpty then s else { s with relIds := s.relIds ++ ["rIdC"] } }
  return { name, kind, what, wb := tabled, pkg := { base with rels, parts, overrides } }

def factsTable : Table := { name := "Facts", range := ⟨⟨1, 1⟩, ⟨3, 6⟩⟩, columns := ["Fact", "Value", "Proved by"] }

def limitsWithTables (ts : List Table) (names : List DefinedName := []) : Workbook :=
  { base with sheets := { Example.limits with tables := ts } :: base.sheets.tail, names }
def wbRelsWith (f : List Rel → List Rel) : Package :=
  { lay with rels := lay.rels.map fun (s, rs) => if s = .part workbookPart then (s, f rs) else (s, rs) }

def broken : List Case :=
  let c := Case.ofWorkbook
  [ c "W01-sst-dangling" "broken" "a cell points at shared string 99 of 14"
      (withRows [⟨1, [⟨⟨1, 1⟩, .shared 99, 0, none⟩]⟩])
  , c "W02-cells-unsorted" "broken" "B1 written before A1"
      (withRows [⟨1, [⟨⟨2, 1⟩, .number 2, 0, none⟩, ⟨⟨1, 1⟩, .number 1, 0, none⟩]⟩])
  , c "W03-row-twice" "broken" "row 1 written twice"
      (withRows [⟨1, [⟨⟨1, 1⟩, .number 1, 0, none⟩]⟩, ⟨1, [⟨⟨2, 1⟩, .number 2, 0, none⟩]⟩])
  , c "W04-cell-wrong-row" "broken" "cell A7 inside row 2"
      (withRows [⟨2, [⟨⟨1, 7⟩, .number 7, 0, none⟩]⟩])
  , c "W05-column-XFE" "broken" "column 16385 (XFE), one past the last"
      (withRows [⟨1, [⟨⟨16385, 1⟩, .number 1, 0, none⟩]⟩])
  , c "W06-row-1048577" "broken" "row 1048577, one past the last"
      (withRows [⟨1048577, [⟨⟨1, 1048577⟩, .number 1, 0, none⟩]⟩])
  , c "W07-name-32" "broken" "sheet name of 32 characters"
      (withSheetName "ABCDEFGHIJKLMNOPQRSTUVWXYZ123456")
  , c "W08-name-slash" "broken" "sheet name containing /"
      (withSheetName "Q1/Q2")
  , c "W09-name-case-clash" "broken" "sheets 'Limits' and 'LIMITS'"
      { base with sheets := [Example.limits, { Example.columns with name := "LIMITS" }] }
  , c "W10-name-empty" "broken" "empty sheet name" (withSheetName "")
  , c "W11-style-dangling" "broken" "style 5 of 2" (withRows [⟨1, [⟨⟨1, 1⟩, .number 1, 5, none⟩]⟩])
  , c "W12-no-sheets" "broken" "a workbook with no sheets" { base with sheets := [] }
  , { name := "P01-rel-dangling", kind := "broken", what := "worksheet relationship to sheet9.xml, which is not there"
      wb := base, pkg := wbRelsWith fun rs => rs.map fun r =>
        if r.id = rid 1 then { r with target := ⟨["worksheets"], "sheet9", ["xml"]⟩ } else r }
  , { name := "P02-workbook-untyped", kind := "broken", what := "no Override for the workbook: it falls to Default application/xml"
      wb := base, pkg := { lay with overrides := lay.overrides.filter (·.1 != workbookPart) } }
  , { name := "P03-rid-twice", kind := "broken", what := "two relationships with id rId1"
      wb := base, pkg := wbRelsWith fun rs => rs.map fun r => if r.id = rid 2 then { r with id := rid 1 } else r }
  , { name := "P04-two-main", kind := "broken", what := "two officeDocument relationships"
      wb := base, pkg := { lay with rels := lay.rels.map fun (s, rs) =>
        if s = .package then (s, rs ++ [⟨"rId2", .officeDocument, stylesPart, false, false⟩]) else (s, rs) } }
  , { name := "P05-orphan-part", kind := "probe", what := "a part nothing points at (ECMA-376-1 §9.1.4: readers ignore it)"
      wb := base, pkg := { lay with parts := lay.parts ++ [⟨["xl"], "orphan", ["xml"]⟩] } }
  , { name := "P06-entry-twice", kind := "broken", what := "sheet1.xml in the archive twice"
      wb := base, pkg := { lay with parts := lay.parts ++ [sheetPart 1] } }
  , { name := "P07-no-content-type", kind := "broken", what := "a reachable part with extension .bin and no content type"
      wb := base, pkg := { (wbRelsWith fun rs => rs ++ [⟨"rId99", .theme, ⟨["theme"], "theme1", ["bin"]⟩, false, false⟩]) with
        parts := lay.parts ++ [⟨["xl", "theme"], "theme1", ["bin"]⟩] } }
  , c "W13-same-cell-twice" "broken" "A1 written twice in one row, with 1 and then 2"
      (withRows [⟨1, [⟨⟨1, 1⟩, .number 1, 0, none⟩, ⟨⟨1, 1⟩, .number 2, 0, none⟩]⟩])
  , c "W14-dimension-too-small" "probe" "dimension A1:B2 on a sheet with cells to C8 (a writer rule: readers ignore it)"
      (withLimits fun s => { s with dimension := some (Range.mk ⟨1, 1⟩ ⟨2, 2⟩) })
  , c "W15-merges-overlap" "broken" "merged A1:B2 and B2:C3"
      (withLimits fun s => { s with merges := [Range.mk ⟨1, 1⟩ ⟨2, 2⟩, Range.mk ⟨2, 2⟩ ⟨3, 3⟩] })
  , c "W16-merge-backwards" "broken" "merged C3:A1, corners reversed"
      (withLimits fun s => { s with merges := [Range.mk ⟨3, 3⟩ ⟨1, 1⟩] })
  , { name := "P09-names-differ-by-case", kind := "broken", what := "/xl/workbook.xml and /xl/Workbook.xml: one name to OPC"
      wb := base, pkg := { (wbRelsWith fun rs => rs ++ [⟨"rId98", .theme, ⟨[], "Workbook", ["xml"]⟩, false, false⟩]) with
        parts := lay.parts ++ [⟨["xl"], "Workbook", ["xml"]⟩] } }
  , { name := "P08-sheet-typed-styles", kind := "broken", what := "sheet1.xml typed as a styles part"
      wb := base, pkg := { lay with overrides := lay.overrides.map (fun p =>
        (if p.1 = sheetPart 1 then (p.1, stylesType) else p)) } }
  ]

def probes : List Case :=
  let c := Case.ofWorkbook
  let ctl := String.singleton (Char.ofNat 1)
  [ c "G01-control-char-shared" "gap" "U+0001 in a shared string" (shd s!"a{ctl}b")
  , c "G02-control-char-inline" "gap" "U+0001 in an inline string" (inl s!"a{ctl}b")
  , c "G03-nonchar-FFFE" "gap" "U+FFFE in a string" (inl s!"a{Char.ofNat 0xFFFE}b")
  , c "G04-spaces-inline" "probe" "leading and trailing spaces, inline" (inl "  pad  ")
  , c "G05-spaces-shared" "probe" "leading and trailing spaces, shared" (shd "  pad  ")
  , c "G06-crlf-shared" "probe" "CR LF inside a shared string" (shd "a\r\nb")
  , c "G07-cr-inline" "probe" "a lone CR inside an inline string" (inl "a\rb")
  , c "G08-tab-newline" "probe" "tab and newline, inline" (inl "a\tb\nc")
  , c "G09-long-string" "gap" "a string of 40000 characters (Excel's limit is 32767)"
      (shd (String.ofList (List.replicate 40000 'x')))
  , c "G10-name-apostrophe" "gap" "sheet name starting with an apostrophe" (withSheetName "'Quoted")
  , c "G11-name-History" "gap" "sheet named History (Excel reserves it)" (withSheetName "History")
  , c "G12-name-emoji-31" "gap" "16 emoji: 16 characters, 32 UTF-16 units"
      (withSheetName (String.ofList (List.replicate 16 (Char.ofNat 0x1F642))))
  , c "G13-int-2^53+1" "gap" "the integer 2^53 + 1" (numw (2 ^ 53 + 1))
  , c "G14-int-10^400" "gap" "the integer 10^400" (numw (10 ^ 400))
  , c "G15-astral" "probe" "an emoji and CJK text" (inl "日本 🙂")
  , c "G16-markup" "probe" "XML specials in text and sheet name"
      { (inl "<b>&amp;\"'</b>") with sheets := [{ name := "A&B <x>", rows := [⟨1, [⟨⟨1, 1⟩, .inline "<b>&amp;\"'</b>", 0, none⟩]⟩] }] }
  , c "G17-empty-sheet" "probe" "a sheet with no rows" { sheets := [{ name := "Empty", rows := [] }], sst := [], styleCount := 1 }
  , c "G18-many-sheets" "probe" "255 sheets"
      { sheets := (List.range' 1 255).map fun (i : Nat) => { name := s!"S{i}", rows := [⟨1, [⟨⟨1, 1⟩, .number (i : Int), 0, none⟩]⟩] }, sst := [], styleCount := 1 }
  , c "G19-formula-looking" "probe" "text =1+1 stored as a string" (inl "=1+1")
  , c "G20-empty-string" "probe" "an empty shared string" (shd "")
  , c "G21-merges-and-dimension" "probe" "dimension A1:D8, merges A7:C7, D1:D3 and the sheet's own A8:C8"
      (withLimits fun s => { s with
        dimension := some (Range.mk ⟨1, 1⟩ ⟨4, 8⟩)
        merges := s.merges ++ [Range.mk ⟨1, 7⟩ ⟨3, 7⟩, Range.mk ⟨4, 1⟩ ⟨4, 3⟩] })
  , c "W17-value-under-merge" "broken" "B1 holds a value under the merge A1:B1"
      (withLimits fun s => { s with merges := [Range.mk ⟨1, 1⟩ ⟨2, 1⟩] })
  , c "W18-numfmt-undeclared" "broken" "a style with numFmtId 200, never declared"
      { base with styleCount := 2, xfFormats := [0, 200] }
  , c "W19-date-out-of-range" "broken" "a date format on 3000000 (past 9999-12-31) and on -1"
      { (oneCellRow [⟨⟨1, 1⟩, .number 3000000, 1, none⟩, ⟨⟨2, 1⟩, .number (-1), 1, none⟩]) with
          styleCount := 2, xfFormats := [0, 14] }
  , c "W20-numfmt-twice" "broken" "numFmtId 164 declared twice"
      { base with numFmts := [(164, "yyyy"), (164, "mm")] }
  , c "G24-dates-1900" "probe" "serials 0, 1, 59, 60, 61, 45000 in 1900 dates, a time, a custom format"
      { (oneCellRow [⟨⟨1, 1⟩, .number 0, 1, none⟩, ⟨⟨2, 1⟩, .number 1, 1, none⟩, ⟨⟨3, 1⟩, .number 59, 1, none⟩,
          ⟨⟨4, 1⟩, .number 60, 1, none⟩, ⟨⟨5, 1⟩, .number 61, 1, none⟩, ⟨⟨6, 1⟩, .number 45000, 2, none⟩,
          ⟨⟨7, 1⟩, .real 450005 (-1), 3, none⟩, ⟨⟨8, 1⟩, .number 2958465, 2, none⟩]) with
          styleCount := 4, numFmts := [(164, "yyyy-mm-dd")], xfFormats := [0, 14, 164, 22] }
  , c "G25-dates-1904" "probe" "serials 0, 1, 45000 in the 1904 date system"
      { (oneCellRow [⟨⟨1, 1⟩, .number 0, 1, none⟩, ⟨⟨2, 1⟩, .number 1, 1, none⟩, ⟨⟨3, 1⟩, .number 45000, 1, none⟩]) with
          styleCount := 2, xfFormats := [0, 14], date1904 := true }
  , c "W21-all-hidden" "broken" "both sheets hidden"
      { base with sheets := base.sheets.map fun s => { s with state := .hidden } }
  , c "G26-one-hidden" "probe" "one sheet very hidden, one visible"
      { base with sheets := match base.sheets with
          | s :: rest => { s with state := .veryHidden } :: rest
          | [] => [] }
  , c "W22-name-like-a-cell" "broken" "defined names A1 and R1C1"
      { base with names := [{ name := "A1", formula := "Limits!$B$2" }, { name := "R1C1", formula := "Limits!$B$3" }] }
  , c "W23-name-with-space" "broken" "a defined name with a space"
      { base with names := [{ name := "Last Row", formula := "Limits!$B$4" }] }
  , c "W24-names-case-clash" "broken" "defined names Total and TOTAL"
      { base with names := [{ name := "Total", formula := "1" }, { name := "TOTAL", formula := "2" }] }
  , c "W25-name-bad-scope" "broken" "a name scoped to sheet 5 of 2"
      { base with names := [{ name := "Local", scope := some 5, formula := "1" }] }
  , c "G27-names" "probe" "workbook and sheet-scoped names, a print area, XFE1 (past XFD, so a name)"
      { base with names := [{ name := "LastColumn", formula := "Limits!$B$2" },
          { name := "LastColumn", scope := some 1, formula := "Columns!$A$11" },
          { name := "_xlnm.Print_Area", scope := some 0, formula := "Limits!$A$1:$C$8" },
          { name := "XFE1", formula := "16385" }] }
  , withTables "G28-table" "probe" "a table over A1:C6 whose header row shows its column names"
      (limitsWithTables [factsTable])
  , withTables "W26-table-header" "broken" "a table whose second column is named Amount, over a header cell that says Value"
      (limitsWithTables [{ factsTable with columns := ["Fact", "Amount", "Proved by"] }])
  , withTables "W27-tables-overlap" "broken" "tables at A1:C6 and B2:C3"
      (limitsWithTables [factsTable, { name := "Inner", range := ⟨⟨2, 2⟩, ⟨3, 3⟩⟩, header := false, columns := ["x", "y"] }])
  , withTables "W28-table-over-merge" "broken" "a table at A7:C8 over the merge A8:C8"
      (limitsWithTables [{ name := "Footer", range := ⟨⟨1, 7⟩, ⟨3, 8⟩⟩, header := false, columns := ["a", "b", "c"] }])
  , withTables "W29-table-name-clash" "broken" "a table and a defined name both called Facts"
      (limitsWithTables [factsTable] [{ name := "FACTS", formula := "Limits!$A$1" }])
  , withTables "W30-table-columns-twice" "broken" "a table with columns Fact and fact"
      (limitsWithTables [{ name := "Twice", range := ⟨⟨1, 2⟩, ⟨2, 6⟩⟩, header := false, columns := ["Fact", "fact"] }])
  , withTables "G29-hyperlinks" "probe" "a hyperlink to a web address and one to a cell of the other sheet"
      (withLimits fun s => { s with
        hyperlinks := [{ ref := ⟨⟨1, 2⟩, ⟨1, 2⟩⟩, rid := some "rIdL1" }, { ref := ⟨⟨1, 3⟩, ⟨1, 3⟩⟩, location := some "Columns!B11" }]
        relIds := ["rIdL1"] })
  , withTables "W31-hyperlink-dangling" "broken" "a hyperlink whose r:id names no relationship"
      (withLimits fun s => { s with hyperlinks := [{ ref := ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, rid := some "rId9" }] })
  , withTables "W32-hyperlink-nowhere" "probe" "a hyperlink with neither r:id nor location (the schema allows it)"
      (withLimits fun s => { s with hyperlinks := [{ ref := ⟨⟨1, 1⟩, ⟨1, 1⟩⟩ }] })
  , c "W33-font-dangling" "broken" "style 1 uses fontId 9 of 2"
      { base with xfRefs := [(0, 0, 0), (9, 0, 0)] }
  , c "W34-cf-dxf-dangling" "broken" "a conditional format with dxfId 7, and no dxfs"
      (withLimits fun s => { s with condFormats := [{ sqref := "B2:B5", dxfIds := [7] }] })
  , c "W35-dv-bad-range" "broken" "a data validation over \"ZZZZ9 A0\""
      (withLimits fun s => { s with validations := [{ sqref := "ZZZZ9 A0", kind := "list" }] })
  , withTables "W36-comment-author" "broken" "a comment by author 5 of 1"
      (withLimits fun s => { s with comments := [{ ref := "A1", author := 5 }], authors := 1 })
  , c "W37-shared-no-master" "broken" "B2 follows shared formula 0, which has no master"
      (withLimits fun s => { s with shared := [{ si := 0, cell := ⟨2, 2⟩ }] })
  , c "W38-cols-overlap" "broken" "column ranges A:C and B:D"
      (withLimits fun s => { s with cols := [(1, 3), (2, 4)] })
  , withTables "G30-more-content" "probe" "a conditional format with its dxf, a validation, a comment, a shared formula, columns"
      { (withLimits fun s => { s with
          condFormats := [{ sqref := "B2:B5 C2", dxfIds := [0] }]
          validations := [{ sqref := "C2:C6", kind := "list" }]
          comments := [{ ref := "A1", author := 0 }]
          authors := 1
          shared := [{ si := 0, cell := ⟨2, 2⟩, master := some (⟨⟨2, 2⟩, ⟨2, 4⟩⟩, "1+1") }, { si := 0, cell := ⟨2, 4⟩ }]
          cols := [(1, 1), (2, 3)] }) with dxfCount := 1 }
  , c "G22-decimals" "probe" "decimals 3.25, 1E-3, -6.02E23, and an error value"
      (oneCellRow [⟨⟨1, 1⟩, .real 325 (-2), 0, none⟩, ⟨⟨2, 1⟩, .real 1 (-3), 0, none⟩,
        ⟨⟨3, 1⟩, .real (-602) 21, 0, none⟩, ⟨⟨4, 1⟩, .error "#N/A", 0, none⟩])
  , c "G23-formula-cached" "probe" "formulas with cached number and text results"
      (oneCellRow [⟨⟨1, 1⟩, .number 2, 0, some "1+1"⟩, ⟨⟨2, 1⟩, .inline "ab", 0, some "\"a\"&\"b\""⟩])
  , c "G31-xstring-shared" "probe" "a shared string that looks like an escape: _x0041_ and _x005F_"
      (shd "_x0041_ and _x005F_")
  , c "G32-xstring-inline" "probe" "an inline string that looks like an escape: a_x000a_b"
      (inl "a_x000a_b")
  , c "G33-xstring-name" "probe" "a sheet named _x0041_" (withSheetName "_x0041_")
  , c "G34-xstring-result" "probe" "a formula whose cached text result is _x0042_"
      (oneCellRow [⟨⟨1, 1⟩, .inline "_x0042_", 0, some "\"_x0042_\""⟩])
  , c "G35-x005F-plain" "probe" "a shared string with x005F_ in it, not an escape: ax005F_b"
      (shd "ax005F_b")
  ]

/-! ## Random well-formed workbooks -/

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def pool : List String :=
  ["hello", "A & B", "<tag>", "\"quoted\"", "it's", "café", "日本語", "🙂 ok", "x y",
   "multi\nline", "tab\there", "", "  lead", "trail  ", "=1+1", "1e5", "TRUE", "-0"]

def pick {α} [Inhabited α] (xs : List α) (s : Nat) : α := xs[s % xs.length]!

/-- One random workbook. It is well-formed by construction; `fuzzCase` checks that too. -/
def randomWorkbook (seed : Nat) : Workbook := Id.run do
  let mut s := lcg (seed + 1)
  let mut sst : List String := []
  let mut sheets : List Sheet := []
  let nSheets := 1 + seed % 3
  for si in [0:nSheets] do
    let mut rows : List Row := []
    let mut r := 0
    s := lcg s
    let nRows := 1 + s % 12
    for _ in [0:nRows] do
      s := lcg s
      r := r + 1 + s % 3
      let mut cells : List Cell := []
      let mut col := 0
      s := lcg s
      let nCells := 1 + s % 6
      for _ in [0:nCells] do
        s := lcg s
        col := col + 1 + s % 30
        s := lcg s
        let v : Stored := match s % 5 with
          | 0 => .number ((lcg s % 2000001 : Nat) - 1000000 : Int)
          | 1 => .bool (s % 2 == 0)
          | 2 => .inline (pick pool (lcg s))
          | _ =>
            let t := pick pool (lcg s)
            match sst.idxOf? t with
            | some i => .shared i
            | none => .shared sst.length
        if let .shared i := v then
          if i == sst.length then sst := sst ++ [pick pool (lcg s)]
        cells := cells ++ [⟨⟨col, r⟩, v, if s % 7 == 0 then 1 else 0, none⟩]
      rows := rows ++ [⟨r, cells⟩]
    sheets := sheets ++ [{ name := s!"Fuzz {seed}-{si + 1}", rows }]
  return { sheets, sst, styleCount := 2 }

def fuzz (n : Nat) : List Case :=
  (List.range n).map fun i => Case.ofWorkbook s!"F{i}" "fuzz" "random well-formed workbook" (randomWorkbook i)

/-! ## The manifest -/

def valueJson : Option Value → Json
  | some (.number n) => Json.mkObj [("t", "n"), ("v", toString n)]
  | some (.text s) => Json.mkObj [("t", "s"), ("v", s)]
  | some (.bool b) => Json.mkObj [("t", "b"), ("v", toJson b)]
  | some (.real m e) => Json.mkObj [("t", "r"), ("m", toString m), ("e", toString e)]
  | some (.error c) => Json.mkObj [("t", "e"), ("v", c)]
  | some .empty => Json.mkObj [("t", "empty")]
  | none => Json.mkObj [("t", "missing")]

/-- Our verdict: every reading rule holds. -/
def Case.accepted (c : Case) : Bool :=
  c.pkg.check && conformsCheck c.pkg c.wb.sheets.length && c.wb.check

/-- What the spec is meant to say about the case. `gap` cases were accepted by the first
version of the spec and are rejected by the current one. -/
def Case.expectAccept (c : Case) : Bool := c.kind == "probe" || c.kind == "fuzz"

def Case.manifest (c : Case) : Json :=
  Json.mkObj [("name", c.name), ("kind", c.kind), ("what", c.what),
    ("orphan_check", toJson c.pkg.orphanCheck),
    ("package_check", toJson c.pkg.check),
    ("conforms_check", toJson (conformsCheck c.pkg c.wb.sheets.length)),
    ("workbook_check", toJson c.wb.check),
    ("names", Json.arr (c.wb.names.toArray.map fun d => Json.str d.name)),
    ("sheets", Json.arr (c.wb.sheets.map fun s => Json.mkObj [("name", s.name),
      ("tables", Json.arr (s.tables.toArray.map fun t => Json.str t.name)),
      ("cells", Json.arr (s.rows.flatMap fun r => r.cells.map fun cell =>
        Json.mkObj [("ref", cell.ref.toA1), ("value",
          Read.withDate c.wb cell (valueJson (cell.stored.resolve c.wb.sst)))]).toArray)]).toArray)]

end Lab
