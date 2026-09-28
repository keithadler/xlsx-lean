import Lean.Data.Json
import Xlsx.Read.Model

/-!
# Saying what is wrong, and where

The verdict comes from the checkers that are proved sound: `Package.check`,
`conformsCheck`, `Workbook.check`, and the writer rule `Package.orphanCheck`. They
answer yes or no. The functions here say *which* rule failed and *where*: which part,
which relationship, which cell. They restate the same rules, one violation at a time;
the adversarial corpus checks on every file that they find nothing exactly when the
checker says yes.
-/

open Lean

namespace Xlsx.Read

structure Problem where
  rule : String
  place : String
  text : String

def packageProblems (p : Package) : Array Problem := Id.run do
  let mut out : Array Problem := #[]
  -- names_unique
  let all := p.allParts
  for (i, n) in (List.range all.length).zip all do
    if let some m := (all.take i).find? (·.key == n.key) then
      out := out.push ⟨"names_unique", n.entryName,
        if m == n then "in the archive twice" else s!"the same name as {m.entryName}, ignoring case"⟩
  -- typed
  for n in all do
    if (p.contentType n).isNone then
      out := out.push ⟨"typed", n.entryName, s!"no content type: no Override, and no Default for .{n.ext}"⟩
  for (s, rs) in p.rels do
    let where_ := s.relsPart.entryName
    if let .part n := s then
      unless p.hasB n do
        out := out.push ⟨"sources_exist", where_, s!"relationships for {n.entryName}, which is not in the archive"⟩
    for r in rs do
      let t := r.resolve s.dir
      unless p.hasB t do
        out := out.push ⟨"targets_exist", where_, s!"{r.id} points at {t.entryName}, which is not in the archive"⟩
    let ids := rs.map (·.id)
    for (i, id) in (List.range ids.length).zip ids do
      if (ids.take i).contains id then
        out := out.push ⟨"ids_unique", where_, s!"id {id} is used twice"⟩
  match p.mainDocument with
  | [_] => pure ()
  | [] => out := out.push ⟨"one_main", "_rels/.rels", "no officeDocument relationship: nothing says where the workbook is"⟩
  | ms => out := out.push ⟨"one_main", "_rels/.rels", s!"{ms.length} officeDocument relationships: " ++ ", ".intercalate (ms.map (·.entryName))⟩
  return out

def conformsProblems (p : Package) (sheets : Nat) : Array Problem := Id.run do
  let mut out : Array Problem := #[]
  for m in p.mainDocument do
    match p.contentType m with
    | some t => if t != workbookType then out := out.push ⟨"main_is_workbook", m.entryName, s!"the main document is typed {t}"⟩
    | none => out := out.push ⟨"main_is_workbook", m.entryName, "the main document has no content type"⟩
    let rs := p.relsOf (.part m)
    let ws := rs.filter (·.type == .worksheet)
    if ws.length != sheets then
      out := out.push ⟨"one_rel_per_sheet", m.entryName, s!"{ws.length} worksheet relationships for {sheets} worksheets"⟩
    for r in ws do
      let t := r.resolve m.dir
      if p.contentType t != some worksheetType then
        out := out.push ⟨"sheets_typed", t.entryName, s!"a worksheet typed {(p.contentType t).getD "(nothing)"}"⟩
  return out

def orphanProblems (p : Package) : Array Problem :=
  let f := p.found p.parts.length
  (p.parts.filter (fun n => !f.any (·.key == n.key))).toArray.map fun n => ⟨"NoOrphans", n.entryName, "no relationship leads here (readers ignore it)"⟩

def cellProblems (wb : Workbook) (row : Row) (c : Cell) (place : String) : Array Problem := Id.run do
  let mut out : Array Problem := #[]
  let a1 := if 0 < c.ref.col && 0 < c.ref.row then c.ref.toA1 else s!"(col {c.ref.col}, row {c.ref.row})"
  let at_ := s!"{place}!{a1}"
  if c.ref.row != row.index then out := out.push ⟨"in_row", at_, s!"written inside row {row.index}"⟩
  if c.ref.col == 0 || c.ref.col > maxCol then out := out.push ⟨"col_le", at_, s!"column {c.ref.col}; the last is {maxCol} (XFD)"⟩
  match c.stored with
  | .shared i => if i ≥ wb.sst.length then out := out.push ⟨"shared_ok", at_, s!"shared string {i}; the table has {wb.sst.length}"⟩
  | .number n => if n.natAbs ≥ maxNumber then out := out.push ⟨"number_ok", at_, s!"{n} has more than 15 digits"⟩
  | .inline t => if !textOk t then out := out.push ⟨"inline_ok", at_, textWhy t⟩
  | .real m e => if !realOk m e then out := out.push ⟨"real_ok", at_, s!"{m}E{e} is not a finite double"⟩
  | .error code => if !errorCodes.contains code then out := out.push ⟨"error_ok", at_, s!"{code} is not an error value"⟩
  | .bool _ | .empty => pure ()
  if c.style ≥ wb.styleCount then out := out.push ⟨"style_ok", at_, s!"style {c.style}; styles.xml has {wb.styleCount}"⟩
  if let some f := c.formula then
    if !textOk f then out := out.push ⟨"formula_ok", at_, textWhy f⟩
  return out
where
  textWhy (t : String) : String :=
    match t.toList.find? (!xmlChar ·) with
    | some ch => s!"contains U+{String.ofList (Nat.toDigits 16 ch.toNat) |>.toUpper}, which XML cannot carry"
    | none => s!"{utf16Length t} characters; the limit is {maxText}"

def workbookProblems (wb : Workbook) (sheetEntries : Array (String × String)) : Array Problem := Id.run do
  let mut out : Array Problem := #[]
  if wb.sheets.isEmpty then out := out.push ⟨"has_sheet", "workbook", "no worksheets"⟩
  if wb.styleCount == 0 then out := out.push ⟨"has_style", "styles", "cellXfs is empty"⟩
  for (i, t) in (List.range wb.sst.length).zip wb.sst do
    if !textOk t then out := out.push ⟨"sst_ok", s!"sharedStrings #{i}", cellProblems.textWhy t⟩
  let keys := wb.sheets.map Sheet.key
  for (i, s) in (List.range wb.sheets.length).zip wb.sheets do
    if (keys.take i).contains s.key then out := out.push ⟨"names_unique", s.name, "a sheet of this name exists already (names ignore case)"⟩
  for s in wb.sheets do
    let place := s.name
    let n := s.name.toList
    if n.isEmpty then out := out.push ⟨"name_nonempty", "(unnamed)", "a sheet with an empty name"⟩
    if utf16Length s.name > 31 then out := out.push ⟨"name_short", place, s!"{utf16Length s.name} UTF-16 units; the limit is 31"⟩
    for ch in n do
      if forbiddenInSheetName.contains ch then out := out.push ⟨"name_chars", place, s!"contains {ch}"⟩
      else if !xmlChar ch then out := out.push ⟨"name_chars", place, "contains a character XML cannot carry"⟩
    if n.head? == some '\'' || n.getLast? == some '\'' then out := out.push ⟨"name_quotes", place, "starts or ends with an apostrophe"⟩
    if s.key == "history".toList then out := out.push ⟨"name_reserved", place, "History is reserved"⟩
    let mut prev : Option Nat := none
    for r in s.rows do
      if r.index == 0 || r.index > maxRow then out := out.push ⟨"index_le", s!"{place} row {r.index}", s!"row {r.index}; rows run 1 to {maxRow}"⟩
      if let some p := prev then
        if r.index ≤ p then out := out.push ⟨"sorted", s!"{place} row {r.index}", s!"comes after row {p}"⟩
      prev := some r.index
      let mut prevCol : Option Nat := none
      for c in r.cells do
        out := out ++ cellProblems wb r c place
        if let some p := prevCol then
          if c.ref.col ≤ p then
            out := out.push ⟨"sorted", s!"{place}!{c.ref.toA1}", if c.ref.col == p then "the same cell again" else s!"written after column {p}"⟩
        prevCol := some c.ref.col
  let _ := sheetEntries
  return out

structure Verdict where
  package : Bool
  conforms : Bool
  workbook : Bool
  orphans : Bool
  problems : Array Problem

def Loaded.verdict (l : Loaded) : Verdict :=
  let n := l.wb.sheets.length
  { package := l.pkg.check, conforms := conformsCheck l.pkg n, workbook := l.wb.check,
    orphans := l.pkg.orphanCheck,
    problems := packageProblems l.pkg ++ conformsProblems l.pkg n ++ workbookProblems l.wb l.sheetEntries
      ++ orphanProblems l.pkg }

def Verdict.ok (v : Verdict) : Bool := v.package && v.conforms && v.workbook

def Severity.label : Severity → String
  | .error => "error" | .unmodeled => "not modeled" | .info => "info"

def reportText (path : String) (l : Loaded) : String := Id.run do
  let v := l.verdict
  let mark (b : Bool) := if b then "✓" else "✗"
  let errs := l.notes.filter (·.severity == .error)
  let cells := l.wb.sheets.foldl (fun a s => a + s.rows.foldl (fun b r => b + r.cells.length) 0) 0
  let pl (n : Nat) (w : String) := s!"{n} {w}{if n == 1 then "" else "s"}"
  let mut s := s!"{path}\n  {l.entries} {if l.entries == 1 then "entry" else "entries"}, {pl l.wb.sheets.length "worksheet"}, {pl cells "cell"}, {pl l.wb.sst.length "shared string"}\n"
  s := s ++ s!"  {mark v.package} package       Package.check        (OPC: names, content types, relationships, one main document)\n"
  s := s ++ (if l.pkg.mainDocument.isEmpty then "  - spreadsheet   conformsCheck        (nothing to check: there is no main document)\n"
    else s!"  {mark v.conforms} spreadsheet   conformsCheck        (the main document is a workbook, one typed worksheet per sheet)\n")
  s := s ++ s!"  {mark v.workbook} workbook      Workbook.check       (sheets, rows, cells, shared strings, styles, Excel's limits)\n"
  s := s ++ s!"  {if v.orphans then "✓" else "!"} writer rule   Package.orphanCheck  (every part reachable; readers ignore orphans)\n"
  unless errs.isEmpty do
    s := s ++ s!"  ✗ reader        {errs.size} problem(s) reading the file\n"
  let shown := v.problems.toList.take 40
  unless shown.isEmpty do
    s := s ++ "\n  where:\n"
    for p in shown do s := s ++ s!"    [{p.rule}] {p.place}: {p.text}\n"
    if v.problems.size > 40 then s := s ++ s!"    … and {v.problems.size - 40} more\n"
  unless l.notes.isEmpty do
    s := s ++ "\n  notes:\n"
    for n in l.notes.toList.take 30 do s := s ++ s!"    {n.severity.label}: {n.place}: {n.text}\n"
    if l.notes.size > 30 then s := s ++ s!"    … and {l.notes.size - 30} more\n"
  let ok := v.ok && errs.isEmpty
  s := s ++ s!"\n  verdict: {if ok then "follows every rule of the spec" else "breaks the spec"}\n"
  return s

def reportJson (path : String) (l : Loaded) : Json :=
  let v := l.verdict
  Json.mkObj [("path", path), ("package_check", toJson v.package), ("conforms_check", toJson v.conforms),
    ("workbook_check", toJson v.workbook), ("orphan_check", toJson v.orphans),
    ("reader_errors", toJson (l.notes.filter (·.severity == .error)).size),
    ("problems", Json.arr (v.problems.map fun p => Json.mkObj [("rule", p.rule), ("place", p.place), ("text", p.text)])),
    ("notes", Json.arr (l.notes.map fun n => Json.mkObj [("severity", n.severity.label), ("place", n.place), ("text", n.text)])),
    ("sheets", Json.arr (l.wb.sheets.toArray.map fun s => Json.mkObj [("name", s.name),
      ("cells", Json.arr (s.rows.toArray.flatMap fun r => r.cells.toArray.map fun c =>
        Json.mkObj [("ref", if 0 < c.ref.col && 0 < c.ref.row then c.ref.toA1 else ""),
          ("value", match c.stored.resolve l.wb.sst with
            | some (.number n) => Json.mkObj [("t", "n"), ("v", toString n)]
            | some (.real m e) => Json.mkObj [("t", "r"), ("m", toString m), ("e", toString e)]
            | some (.text t) => Json.mkObj [("t", "s"), ("v", t)]
            | some (.bool b) => Json.mkObj [("t", "b"), ("v", toJson b)]
            | some (.error c) => Json.mkObj [("t", "e"), ("v", c)]
            | some .empty => Json.mkObj [("t", "empty")]
            | none => Json.mkObj [("t", "missing")])]))]))]

end Xlsx.Read
