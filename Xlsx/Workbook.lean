import Xlsx.Package
import Xlsx.Dates

/-!
# The workbook: SpreadsheetML

Inside the package, `/xl/workbook.xml` lists the sheets, each sheet part lists its rows
and cells, and text lives once in `/xl/sharedStrings.xml`: a cell holding text usually
stores only an index into that table (`<c r="A1" t="s"><v>0</v></c>`). Formatting works
the same way, through an index into the `cellXfs` list of `/xl/styles.xml`.

So a workbook is only readable when every index points at something, rows come in
order, and every cell sits in the row it claims. This file models the workbook, states
those rules, writes a checker for them, and proves what they buy: every cell has a
value, and no two cells of a sheet share a reference.
-/

namespace Xlsx

/-- What a cell holds, as someone reading the sheet sees it. -/
inductive Value where
  | number (n : Int)
  /-- `m × 10^e`, a number with a fractional part or an exponent, as written. -/
  | real (m e : Int)
  | text (s : String)
  | bool (b : Bool)
  /-- `#N/A`, `#DIV/0!` and the rest. -/
  | error (code : String)
  /-- A cell that is there for its format only, with no value. -/
  | empty
  deriving DecidableEq, Repr

/-- How a cell's value is written in the sheet part. -/
inductive Stored where
  /-- `<c><v>42</v></c>` -/
  | number (n : Int)
  /-- `<c t="s"><v>3</v></c>`: entry 3 of the shared string table. -/
  | shared (i : Nat)
  /-- `<c t="b"><v>1</v></c>` -/
  | bool (b : Bool)
  /-- `<c t="inlineStr"><is><t>hi</t></is></c>`, or a formula's text result `t="str"` -/
  | inline (s : String)
  /-- `<c><v>3.25</v></c>` or `<v>1E-3</v>`: `m × 10^e`. -/
  | real (m e : Int)
  /-- `<c t="e"><v>#N/A</v></c>` -/
  | error (code : String)
  /-- `<c r="B2" s="1"/>`: a format and no value. -/
  | empty
  deriving DecidableEq, Repr

/-- Read a stored value, looking text up in the shared string table. -/
def Stored.resolve (sst : List String) : Stored → Option Value
  | .number n => some (.number n)
  | .shared i => sst[i]?.map .text
  | .bool b => some (.bool b)
  | .inline s => some (.text s)
  | .real m e => some (.real m e)
  | .error c => some (.error c)
  | .empty => some .empty

structure Cell where
  ref : CellRef
  stored : Stored
  /-- Index into `cellXfs` in `/xl/styles.xml`; `0` is the default format. -/
  style : Nat := 0
  /-- The formula, if the value was computed: `<f>SUM(A1:A3)</f>`. Not evaluated. -/
  formula : Option String := none
  deriving DecidableEq, Repr

structure Row where
  index : Nat
  cells : List Cell
  deriving DecidableEq, Repr

structure Sheet where
  name : String
  rows : List Row
  /-- `<dimension ref="A1:C6"/>`: the used range the sheet claims, if it says one. -/
  dimension : Option Range := none
  /-- `<mergeCell ref="A6:C6"/>`: merged rectangles. -/
  merges : List Range := []
  deriving DecidableEq, Repr

structure Workbook where
  sheets : List Sheet
  sst : List String
  /-- How many entries `cellXfs` has. -/
  styleCount : Nat := 1
  /-- Custom number formats, `<numFmt numFmtId="164" formatCode="yyyy-mm-dd"/>`. -/
  numFmts : List (Nat × String) := []
  /-- The `numFmtId` of each `cellXfs` entry, in order; empty means all General (0). -/
  xfFormats : List Nat := []
  /-- `<workbookPr date1904="1"/>`: serial 0 is 1904-01-01. -/
  date1904 : Bool := false
  deriving DecidableEq, Repr

/-- The number format a style uses. -/
def Workbook.formatOf (wb : Workbook) (style : Nat) : Nat := wb.xfFormats.getD style 0

/-- Does this style show numbers as dates? -/
def Workbook.isDateStyle (wb : Workbook) (style : Nat) : Bool :=
  let id := wb.formatOf style
  Dates.builtinDate id || ((wb.numFmts.lookup id).map Dates.customDate).getD false

/-- A value shown as a date is a date Excel can show: from serial 0 to 9999-12-31
(**Excel**). Only numbers are affected; text in a date-formatted cell is just text. -/
def Stored.dateOk (date1904 : Bool) : Stored → Bool
  | .number n => 0 ≤ n && n ≤ Dates.maxSerial date1904
  | .real m e => match Dates.split m e with
    | some (days, _) => days ≤ Dates.maxSerial date1904
    | none => false
  | _ => true

/-! ## The rules -/

/-! Where each rule comes from is said beside it: **XML** (the file must parse),
**ECMA-376** (the standard), or **Excel** (Microsoft's published limits, which a file
meant to open in Excel has to respect even where the standard is silent). -/

/-- A character XML 1.0 can carry (the `Char` production). U+0000 to U+001F other than
tab, LF and CR cannot appear in an XML document at all, escaped or not, and neither can
U+FFFE or U+FFFF. -/
def xmlChar (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xD || (0x20 ≤ n && n ≤ 0xD7FF)
    || (0xE000 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- Length in UTF-16 code units, which is how Excel counts characters. -/
def utf16Length (s : String) : Nat :=
  s.toList.foldl (fun a c => a + if c.toNat ≥ 0x10000 then 2 else 1) 0

/-- Excel's limit on the text in one cell. -/
def maxText : Nat := 32767

/-- Text a cell may hold: **XML** characters only, at most 32767 of them (**Excel**). -/
def textOk (s : String) : Bool := s.toList.all xmlChar && utf16Length s ≤ maxText

/-- Excel keeps 15 significant digits, so a larger integer does not survive a round trip;
readers that use doubles already lose it past 2^53 (**Excel**). -/
def maxNumber : Nat := 10 ^ 15

/-- The largest finite double, `(2^53 - 1) × 2^971`. -/
def maxDouble : Nat := (2 ^ 53 - 1) * 2 ^ 971

/-- A decimal `m × 10^e` a reader can hold: it is a finite double (**XML Schema**
`xsd:double`, which is what SpreadsheetML numbers are). -/
def realOk (m e : Int) : Bool :=
  e ≤ 400 && (e < 0 || m.natAbs * 10 ^ e.toNat ≤ maxDouble)

/-- The error values: the seven of ECMA-376's formula grammar (`#NULL!` to `#N/A`) and the
ones Excel has added since (`#GETTING_DATA`, `#SPILL!`, …) (**ECMA-376**, **Excel**). -/
def errorCodes : List String :=
  ["#NULL!", "#DIV/0!", "#VALUE!", "#REF!", "#NAME?", "#NUM!", "#N/A", "#GETTING_DATA",
   "#SPILL!", "#CALC!", "#FIELD!", "#BLOCKED!", "#CONNECT!", "#BUSY!", "#UNKNOWN!", "#PYTHON!",
   "#EXTERNAL!"]

/-- Characters Excel refuses in a sheet name. -/
def forbiddenInSheetName : List Char := ['[', ']', ':', '*', '?', '/', '\\']

/-- Sheet names are compared ignoring case: `Sheet1` and `SHEET1` clash. -/
def Sheet.key (s : Sheet) : List Char := s.name.toList.map Char.toLower

/-- A cell obeys the rules of the row it is in. -/
structure Cell.WellFormed (wb : Workbook) (row : Row) (c : Cell) : Prop where
  in_row : c.ref.row = row.index
  col_pos : 0 < c.ref.col
  col_le : c.ref.col ≤ maxCol
  shared_ok : ∀ i, c.stored = .shared i → i < wb.sst.length
  style_ok : c.style < wb.styleCount
  /-- A number keeps all its digits (**Excel**). -/
  number_ok : ∀ n, c.stored = .number n → n.natAbs < maxNumber
  /-- Inline text is writable (**XML**, **Excel**). -/
  inline_ok : ∀ t, c.stored = .inline t → textOk t = true
  /-- A decimal is a finite double (**XML Schema**). -/
  real_ok : ∀ m e, c.stored = .real m e → realOk m e = true
  /-- An error value is one of the known codes (**ECMA-376**, **Excel**). -/
  error_ok : ∀ code, c.stored = .error code → code ∈ errorCodes
  /-- A formula is writable text (**XML**, **Excel**). -/
  formula_ok : ∀ f, c.formula = some f → textOk f = true
  /-- A number in a date format is a date Excel can show (**Excel**). -/
  date_ok : wb.isDateStyle c.style = true → c.stored.dateOk wb.date1904 = true

structure Row.WellFormed (wb : Workbook) (row : Row) : Prop where
  index_pos : 0 < row.index
  index_le : row.index ≤ maxRow
  cells : ∀ c ∈ row.cells, c.WellFormed wb row
  /-- Cells are written left to right, each column once. -/
  sorted : (row.cells.map (·.ref.col)).Pairwise (· < ·)

structure Sheet.WellFormed (wb : Workbook) (s : Sheet) : Prop where
  name_nonempty : s.name.toList ≠ []
  /-- At most 31 UTF-16 units (**Excel**). -/
  name_short : utf16Length s.name ≤ 31
  name_chars : ∀ ch ∈ s.name.toList, ch ∉ forbiddenInSheetName ∧ xmlChar ch = true
  /-- No apostrophe first or last: formulas quote sheet names with it (**Excel**). -/
  name_quotes : s.name.toList.head? ≠ some '\'' ∧ s.name.toList.getLast? ≠ some '\''
  /-- `History` is reserved (**Excel**). -/
  name_reserved : s.key ≠ "history".toList
  rows : ∀ r ∈ s.rows, r.WellFormed wb
  /-- Rows are written top to bottom, each row once. -/
  sorted : (s.rows.map (·.index)).Pairwise (· < ·)
  /-- The claimed used range holds every cell: readers size their grid from it (**ECMA-376**). -/
  dimension_covers : ∀ d, s.dimension = some d → ∀ r ∈ s.rows, ∀ c ∈ r.cells, d.contains c.ref = true
  /-- Every merged range has its corners in order, inside the sheet (**ECMA-376**). -/
  merges_valid : ∀ m ∈ s.merges, m.Valid
  /-- No two merged ranges overlap: Excel drops overlapping merges as a repair (**Excel**). -/
  merges_disjoint : s.merges.Pairwise (fun a b => a.overlaps b = false)
  /-- Under a merge, only the top-left cell holds a value; the rest may carry a format.
  Excel hides the others and openpyxl discards them, so readers would disagree (**Excel**). -/
  merged_hidden_empty : ∀ m ∈ s.merges, ∀ r ∈ s.rows, ∀ c ∈ r.cells,
    m.contains c.ref = true → c.ref ≠ m.first → c.stored = .empty

structure Workbook.WellFormed (wb : Workbook) : Prop where
  has_sheet : wb.sheets ≠ []
  sheets : ∀ s ∈ wb.sheets, s.WellFormed wb
  names_unique : (wb.sheets.map Sheet.key).Nodup
  has_style : 0 < wb.styleCount
  /-- Every shared string is writable (**XML**, **Excel**). -/
  sst_ok : ∀ t ∈ wb.sst, textOk t = true
  /-- Custom number format ids are unique (**ECMA-376**). -/
  numfmt_ids_unique : (wb.numFmts.map (·.1)).Nodup
  /-- `numFmtId` is given for every style, or for none (**ECMA-376**). -/
  xf_formats : wb.xfFormats = [] ∨ wb.xfFormats.length = wb.styleCount
  /-- A style's number format exists: ids below 164 are built in, the rest must be
  declared in `numFmts` (**ECMA-376**, **Excel**). -/
  numfmt_ref : ∀ id ∈ wb.xfFormats, id < 164 ∨ id ∈ wb.numFmts.map (·.1)

/-! ## What the rules buy -/

/-- Every cell of a well-formed workbook has a value: no shared string index dangles. -/
theorem Cell.WellFormed.resolves {wb : Workbook} {row : Row} {c : Cell}
    (h : c.WellFormed wb row) : ∃ v, c.stored.resolve wb.sst = some v := by
  cases hs : c.stored with
  | number n => exact ⟨_, rfl⟩
  | bool b => exact ⟨_, rfl⟩
  | inline s => exact ⟨_, rfl⟩
  | real m e => exact ⟨_, rfl⟩
  | error c => exact ⟨_, rfl⟩
  | empty => exact ⟨_, rfl⟩
  | shared i =>
    have hi := h.shared_ok i hs
    exact ⟨.text wb.sst[i], by simp [Stored.resolve, hi]⟩

/-- Every reference in a sheet, in the order written. -/
def Sheet.refs (s : Sheet) : List CellRef := s.rows.flatMap fun r => r.cells.map (·.ref)

theorem Row.refs_nodup {wb : Workbook} {r : Row} (h : r.WellFormed wb) :
    (r.cells.map (·.ref)).Nodup := by
  have hs := h.sorted
  rw [List.pairwise_map] at hs
  unfold List.Nodup
  rw [List.pairwise_map]
  exact hs.imp fun hlt heq => by rw [heq] at hlt; exact Nat.lt_irrefl _ hlt

theorem rows_refs_nodup {wb : Workbook} :
    ∀ {rows : List Row}, (∀ r ∈ rows, r.WellFormed wb) → (rows.map (·.index)).Pairwise (· < ·) →
      (rows.flatMap fun r => r.cells.map (·.ref)).Nodup
  | [], _, _ => List.nodup_nil
  | r :: rs, hrows, hsorted => by
    rw [List.flatMap_cons]
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hsorted
    refine List.nodup_append.2 ⟨Row.refs_nodup (hrows r (by simp)),
      rows_refs_nodup (fun r' h' => hrows r' (by simp [h'])) hsorted.2, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_map] at ha
    simp only [List.mem_flatMap, List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨r', hr', c', hc', hcc⟩ := hb
    have h1 := ((hrows r (by simp)).cells c hc).in_row
    have h2 := ((hrows r' (by simp [hr'])).cells c' hc').in_row
    have hlt := hsorted.1 r'.index ⟨r', hr', rfl⟩
    rw [← hcc] at h1
    omega

/-- No two cells of a well-formed sheet have the same reference, so "the cell at B7"
always means one cell. -/
theorem Sheet.WellFormed.refs_nodup {wb : Workbook} {s : Sheet} (h : s.WellFormed wb) :
    s.refs.Nodup :=
  rows_refs_nodup h.rows h.sorted

/-- **Every cell is in at most one merged range** of a well-formed sheet. -/
theorem Sheet.WellFormed.merge_unique {wb : Workbook} {s : Sheet} (h : s.WellFormed wb) (c : CellRef) :
    (s.merges.filter (·.contains c)).length ≤ 1 := by
  have hp := h.merges_disjoint
  generalize s.merges = ms at hp
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.pairwise_cons] at hp
    by_cases hm : m.contains c = true
    · have hrest : ms.filter (·.contains c) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hbc
        have := hp.1 b hb
        rw [Range.overlaps_of_contains hm hbc] at this
        cases this
      simp [List.filter_cons, hm, hrest]
    · simp only [List.filter_cons, hm, Bool.false_eq_true, ite_false]
      exact ih hp.2

/-- The value at a reference, found the way a reader finds it. -/
def Sheet.value (sst : List String) (s : Sheet) (ref : CellRef) : Option Value := do
  let row ← s.rows.find? (·.index == ref.row)
  let c ← row.cells.find? (·.ref == ref)
  c.stored.resolve sst

/-! ## The checker -/

/-- Strictly increasing, checked on neighbors. -/
def increasing : List Nat → Bool
  | a :: b :: t => a < b && increasing (b :: t)
  | _ => true

theorem increasing_sound : ∀ {l : List Nat}, increasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := increasing_sound h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

def Cell.check (wb : Workbook) (row : Row) (c : Cell) : Bool :=
  c.ref.row == row.index && 0 < c.ref.col && c.ref.col ≤ maxCol
  && (match c.stored with
      | .shared i => i < wb.sst.length
      | .number n => n.natAbs < maxNumber
      | .inline t => textOk t
      | .real m e => realOk m e
      | .error code => errorCodes.contains code
      | .bool _ | .empty => true)
  && c.style < wb.styleCount
  && (match c.formula with | some f => textOk f | none => true)
  && (!wb.isDateStyle c.style || c.stored.dateOk wb.date1904)

def Row.check (wb : Workbook) (row : Row) : Bool :=
  0 < row.index && row.index ≤ maxRow && row.cells.all (Cell.check wb row)
  && increasing (row.cells.map (·.ref.col))

/-- No two in the list overlap, checked pair by pair. -/
def disjointB : List Range → Bool
  | [] => true
  | m :: ms => ms.all (fun b => !m.overlaps b) && disjointB ms

theorem disjointB_sound : ∀ {ms : List Range}, disjointB ms = true →
    ms.Pairwise (fun a b => a.overlaps b = false)
  | [], _ => List.Pairwise.nil
  | m :: ms, h => by
    simp only [disjointB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact List.pairwise_cons.2 ⟨h.1, disjointB_sound h.2⟩

def Sheet.check (wb : Workbook) (s : Sheet) : Bool :=
  !s.name.toList.isEmpty && utf16Length s.name ≤ 31
  && s.name.toList.all (fun ch => !forbiddenInSheetName.contains ch && xmlChar ch)
  && s.name.toList.head? != some '\'' && s.name.toList.getLast? != some '\''
  && s.key != "history".toList
  && s.rows.all (Row.check wb) && increasing (s.rows.map (·.index))
  && (match s.dimension with
      | some d => s.rows.all fun r => r.cells.all fun c => d.contains c.ref
      | none => true)
  && s.merges.all (fun m => decide m.Valid) && disjointB s.merges
  && s.merges.all (fun m => s.rows.all fun r => r.cells.all fun c =>
      !m.contains c.ref || c.ref == m.first || c.stored == .empty)

def Workbook.check (wb : Workbook) : Bool :=
  !wb.sheets.isEmpty && wb.sheets.all (Sheet.check wb)
  && Package.noDups (wb.sheets.map Sheet.key) && 0 < wb.styleCount
  && wb.sst.all textOk
  && Package.noDups (wb.numFmts.map (·.1))
  && (wb.xfFormats.isEmpty || wb.xfFormats.length == wb.styleCount)
  && wb.xfFormats.all (fun id => id < 164 || (wb.numFmts.map (·.1)).contains id)

theorem Cell.check_sound {wb row c} (h : Cell.check wb row c = true) : c.WellFormed wb row := by
  simp only [Cell.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hi] at h4
    simpa using h4
  · intro n hn
    rw [hn] at h4
    simpa using h4
  · intro t ht
    rw [ht] at h4
    simpa using h4
  · intro m e hme
    rw [hme] at h4
    simpa using h4
  · intro code hc
    rw [hc] at h4
    simpa using h4
  · intro f hf
    rw [hf] at h6
    simpa using h6
  · intro hd
    simp only [hd, Bool.not_true, Bool.false_or] at h7
    exact h7

theorem Row.check_sound {wb row} (h : Row.check wb row = true) : row.WellFormed wb := by
  simp only [Row.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun c hc => Cell.check_sound (h3 c hc), increasing_sound h4⟩

theorem Sheet.check_sound {wb s} (h : Sheet.check wb s = true) : s.WellFormed wb := by
  simp only [Sheet.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hq1⟩, hq2⟩, hh⟩, h4⟩, h5⟩, hd⟩, hm⟩, hmd⟩, hme⟩ := h
  exact {
    name_nonempty := h1
    name_short := h2
    name_chars := fun ch hch => by
      obtain ⟨hf, hx⟩ := h3 ch hch
      refine ⟨fun hbad => ?_, hx⟩
      rw [List.contains_iff_mem.2 hbad] at hf
      cases hf
    name_quotes := ⟨hq1, hq2⟩
    name_reserved := hh
    rows := fun r hr => Row.check_sound (h4 r hr)
    sorted := increasing_sound h5
    dimension_covers := fun d hdim r hr c hc => by
      rw [hdim] at hd
      simp only [List.all_eq_true] at hd
      exact hd r hr c hc
    merges_valid := fun m hmem => hm m hmem
    merges_disjoint := disjointB_sound hmd
    merged_hidden_empty := fun m hm' r hr c hc hin hne => by
      have := hme m hm' r hr c hc
      simp only [hin, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h }

/-- **The checker is sound**: a workbook it accepts follows every rule. -/
theorem Workbook.check_sound {wb : Workbook} (h : wb.check = true) : wb.WellFormed := by
  simp only [Workbook.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun s hs => Sheet.check_sound (h2 s hs), Package.noDups_sound h3, h4, h5,
    Package.noDups_sound h6, ?_, ?_⟩
  · simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq] at h7
    exact h7
  · intro id hid
    have := h8 id hid
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at this
    exact this

end Xlsx
