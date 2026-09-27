import Xlsx.Package

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
  | text (s : String)
  | bool (b : Bool)
  deriving DecidableEq, Repr

/-- How a cell's value is written in the sheet part. -/
inductive Stored where
  /-- `<c><v>42</v></c>` -/
  | number (n : Int)
  /-- `<c t="s"><v>3</v></c>`: entry 3 of the shared string table. -/
  | shared (i : Nat)
  /-- `<c t="b"><v>1</v></c>` -/
  | bool (b : Bool)
  /-- `<c t="inlineStr"><is><t>hi</t></is></c>` -/
  | inline (s : String)
  deriving DecidableEq, Repr

/-- Read a stored value, looking text up in the shared string table. -/
def Stored.resolve (sst : List String) : Stored → Option Value
  | .number n => some (.number n)
  | .shared i => sst[i]?.map .text
  | .bool b => some (.bool b)
  | .inline s => some (.text s)

structure Cell where
  ref : CellRef
  stored : Stored
  /-- Index into `cellXfs` in `/xl/styles.xml`; `0` is the default format. -/
  style : Nat := 0
  deriving DecidableEq, Repr

structure Row where
  index : Nat
  cells : List Cell
  deriving DecidableEq, Repr

structure Sheet where
  name : String
  rows : List Row
  deriving DecidableEq, Repr

structure Workbook where
  sheets : List Sheet
  sst : List String
  /-- How many entries `cellXfs` has. -/
  styleCount : Nat := 1
  deriving DecidableEq, Repr

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

structure Workbook.WellFormed (wb : Workbook) : Prop where
  has_sheet : wb.sheets ≠ []
  sheets : ∀ s ∈ wb.sheets, s.WellFormed wb
  names_unique : (wb.sheets.map Sheet.key).Nodup
  has_style : 0 < wb.styleCount
  /-- Every shared string is writable (**XML**, **Excel**). -/
  sst_ok : ∀ t ∈ wb.sst, textOk t = true

/-! ## What the rules buy -/

/-- Every cell of a well-formed workbook has a value: no shared string index dangles. -/
theorem Cell.WellFormed.resolves {wb : Workbook} {row : Row} {c : Cell}
    (h : c.WellFormed wb row) : ∃ v, c.stored.resolve wb.sst = some v := by
  cases hs : c.stored with
  | number n => exact ⟨_, rfl⟩
  | bool b => exact ⟨_, rfl⟩
  | inline s => exact ⟨_, rfl⟩
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
      | .bool _ => true)
  && c.style < wb.styleCount

def Row.check (wb : Workbook) (row : Row) : Bool :=
  0 < row.index && row.index ≤ maxRow && row.cells.all (Cell.check wb row)
  && increasing (row.cells.map (·.ref.col))

def Sheet.check (wb : Workbook) (s : Sheet) : Bool :=
  !s.name.toList.isEmpty && utf16Length s.name ≤ 31
  && s.name.toList.all (fun ch => !forbiddenInSheetName.contains ch && xmlChar ch)
  && s.name.toList.head? != some '\'' && s.name.toList.getLast? != some '\''
  && s.key != "history".toList
  && s.rows.all (Row.check wb) && increasing (s.rows.map (·.index))

def Workbook.check (wb : Workbook) : Bool :=
  !wb.sheets.isEmpty && wb.sheets.all (Sheet.check wb)
  && Package.noDups (wb.sheets.map Sheet.key) && 0 < wb.styleCount
  && wb.sst.all textOk

theorem Cell.check_sound {wb row c} (h : Cell.check wb row c = true) : c.WellFormed wb row := by
  simp only [Cell.check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, ?_, ?_⟩
  · intro i hi
    rw [hi] at h4
    simpa using h4
  · intro n hn
    rw [hn] at h4
    simpa using h4
  · intro t ht
    rw [ht] at h4
    simpa using h4

theorem Row.check_sound {wb row} (h : Row.check wb row = true) : row.WellFormed wb := by
  simp only [Row.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun c hc => Cell.check_sound (h3 c hc), increasing_sound h4⟩

theorem Sheet.check_sound {wb s} (h : Sheet.check wb s = true) : s.WellFormed wb := by
  simp only [Sheet.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.isEmpty_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hq1⟩, hq2⟩, hh⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, ?_, ⟨hq1, hq2⟩, hh, fun r hr => Row.check_sound (h4 r hr), increasing_sound h5⟩
  intro ch hch
  obtain ⟨hf, hx⟩ := h3 ch hch
  refine ⟨fun hbad => ?_, hx⟩
  rw [List.contains_iff_mem.2 hbad] at hf
  cases hf

/-- **The checker is sound**: a workbook it accepts follows every rule. -/
theorem Workbook.check_sound {wb : Workbook} (h : wb.check = true) : wb.WellFormed := by
  simp only [Workbook.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, fun s hs => Sheet.check_sound (h2 s hs), Package.noDups_sound h3, h4, h5⟩

end Xlsx
