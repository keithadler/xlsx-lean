/-!
# Cell references

A spreadsheet names its columns `A, B, ..., Z, AA, AB, ..., ZZ, AAA, ...`. This is
*bijective base 26*: there is no zero digit, the digits are `A = 1` through `Z = 26`,
and every string of capital letters names exactly one column. XLSX stops at column
16384, which is `XFD`, and at row 1048576.

This file proves the column naming is a bijection between positive numbers and
non-empty letter strings, that the A1 form of a reference (`B7`, `XFD1048576`) can be
read back, and the exact limits.

Digits are `Fin 26`, where digit `d` stands for the letter with value `d + 1`.
-/

namespace Xlsx

/-! ## Bijective base 26 -/

/-- `encodeCol` with explicit fuel, so that it is structural recursion: the kernel can then
evaluate it, and small facts like `colName 16384 = "XFD"` are checked by computation. -/
def encodeColAux : Nat → Nat → List (Fin 26)
  | 0, _ => []
  | _, 0 => []
  | k + 1, n + 1 => encodeColAux k (n / 26) ++ [⟨n % 26, Nat.mod_lt _ (by decide)⟩]

/-- The digits of `n` in bijective base 26, most significant first. `0` has none. -/
def encodeCol (n : Nat) : List (Fin 26) := encodeColAux n n

/-- Enough fuel is enough: any amount at least `n` gives the same digits. -/
theorem encodeColAux_fuel {k k' n : Nat} (hk : n ≤ k) (hk' : n ≤ k') :
    encodeColAux k n = encodeColAux k' n := by
  induction k generalizing k' n with
  | zero => obtain rfl : n = 0 := by omega
            cases k' <;> rfl
  | succ k ih =>
    match n, k' with
    | 0, 0 => rfl
    | 0, _ + 1 => rfl
    | m + 1, 0 => omega
    | m + 1, k'' + 1 =>
      simp only [encodeColAux]
      rw [ih (by omega) (show m / 26 ≤ k'' by omega)]

@[simp] theorem encodeCol_zero : encodeCol 0 = [] := rfl

theorem encodeCol_succ (n : Nat) :
    encodeCol (n + 1) = encodeCol (n / 26) ++ [⟨n % 26, Nat.mod_lt _ (by decide)⟩] := by
  unfold encodeCol
  rw [encodeColAux, encodeColAux_fuel (k' := n / 26) (by omega) (by omega)]

/-- Read bijective base-26 digits back into a number. -/
def decodeCol (ds : List (Fin 26)) : Nat :=
  ds.foldl (fun acc d => acc * 26 + (d.val + 1)) 0

theorem decodeCol_append (ds : List (Fin 26)) (d : Fin 26) :
    decodeCol (ds ++ [d]) = decodeCol ds * 26 + (d.val + 1) := by
  simp [decodeCol, List.foldl_append]

/-- Reading back what was written gives the column number. -/
theorem decodeCol_encodeCol (n : Nat) : decodeCol (encodeCol n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      rw [encodeCol_succ, decodeCol_append, ih (n / 26) (by omega)]
      simp only
      omega

/-- Writing what was read gives the same digits: *every* digit string is some column. -/
theorem encodeCol_decodeCol (ds : List (Fin 26)) : encodeCol (decodeCol ds) = ds := by
  suffices ∀ r : List (Fin 26), encodeCol (decodeCol r.reverse) = r.reverse by
    simpa using this ds.reverse
  intro r
  induction r with
  | nil => rfl
  | cons d r ih =>
    rw [List.reverse_cons, decodeCol_append]
    generalize r.reverse = ds at ih ⊢
    have h : decodeCol ds * 26 + (d.val + 1) = (decodeCol ds * 26 + d.val) + 1 := by omega
    rw [h, encodeCol_succ]
    have hq : (decodeCol ds * 26 + d.val) / 26 = decodeCol ds := by omega
    have hr : (decodeCol ds * 26 + d.val) % 26 = d.val := by omega
    simp only [hq, hr, ih]

theorem encodeCol_injective {m n : Nat} (h : encodeCol m = encodeCol n) : m = n := by
  rw [← decodeCol_encodeCol m, ← decodeCol_encodeCol n, h]

/-- Only column `0` (which does not exist) has no letters. -/
theorem encodeCol_eq_nil {n : Nat} : encodeCol n = [] ↔ n = 0 := by
  constructor
  · intro h; rw [← decodeCol_encodeCol n, h]; rfl
  · rintro rfl; rfl

/-! ## Letters -/

/-- The capital letter for a digit: `0 ↦ 'A'`, `25 ↦ 'Z'`. -/
def letter (d : Fin 26) : Char := Char.ofNat (65 + d.val)

/-- The digit for a capital letter, if it is one. -/
def unletter (c : Char) : Option (Fin 26) :=
  if h : 65 ≤ c.toNat ∧ c.toNat ≤ 90 then
    some ⟨c.toNat - 65, by omega⟩
  else none

theorem unletter_letter : ∀ d : Fin 26, unletter (letter d) = some d := by decide

theorem letter_injective {a b : Fin 26} (h : letter a = letter b) : a = b := by
  have := congrArg unletter h
  rwa [unletter_letter, unletter_letter, Option.some.injEq] at this

/-- Digits are never letters, which is what lets `B7` be split into `B` and `7`. -/
theorem unletter_digitChar : ∀ d : Fin 10, unletter (Nat.digitChar d.val) = none := by decide

/-- Parsing a mapped list of letters recovers the digits. -/
theorem mapM_unletter_map_letter (ds : List (Fin 26)) :
    (ds.map letter).mapM unletter = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.mapM_cons, unletter_letter, ih]

/-! ## Column names -/

/-- The name of column `n` (1-based): `colName 1 = "A"`, `colName 28 = "AB"`. -/
def colName (n : Nat) : String := String.ofList ((encodeCol n).map letter)

/-- Read a column name. Empty strings and anything that is not all capitals fail. -/
def parseCol (s : String) : Option Nat :=
  match s.toList with
  | [] => none
  | cs => (cs.mapM unletter).map decodeCol

theorem parseCol_colName {n : Nat} (hn : 0 < n) : parseCol (colName n) = some n := by
  unfold parseCol colName
  rw [String.toList_ofList]
  have hne : (encodeCol n).map letter ≠ [] := by
    simp [encodeCol_eq_nil]; omega
  split
  · contradiction
  · rw [mapM_unletter_map_letter, Option.map_some, decodeCol_encodeCol]

theorem colName_injective {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : colName m = colName n) : m = n := by
  have := congrArg parseCol h
  rwa [parseCol_colName hm, parseCol_colName hn, Option.some.injEq] at this

/-! ## The limits of a worksheet -/

/-- The last column of an XLSX worksheet, `2 ^ 14`. -/
def maxCol : Nat := 16384
/-- The last row of an XLSX worksheet, `2 ^ 20`. -/
def maxRow : Nat := 1048576

theorem maxCol_eq : maxCol = 2 ^ 14 := rfl
theorem maxRow_eq : maxRow = 2 ^ 20 := rfl

theorem colName_one : colName 1 = "A" := by decide +kernel
theorem colName_26 : colName 26 = "Z" := by decide +kernel
theorem colName_27 : colName 27 = "AA" := by decide +kernel
theorem colName_702 : colName 702 = "ZZ" := by decide +kernel
theorem colName_703 : colName 703 = "AAA" := by decide +kernel
/-- The last column is `XFD`. -/
theorem colName_maxCol : colName maxCol = "XFD" := by decide +kernel
theorem parseCol_XFD : parseCol "XFD" = some maxCol := by decide +kernel

/-- Every column that exists has a name of at most three letters. -/
theorem encodeCol_length_le_three {n : Nat} (h : n ≤ 18278) : (encodeCol n).length ≤ 3 := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [encodeCol_succ]
    match hq : n / 26 with
    | 0 => simp
    | q + 1 =>
      rw [encodeCol_succ]
      match hq' : q / 26 with
      | 0 => simp
      | r + 1 =>
        rw [encodeCol_succ]
        have : r / 26 = 0 := by omega
        simp [this]

/-- `ZZZ` is column 18278, the last with three letters, so `XFD` has room to spare. -/
theorem colName_18278 : colName 18278 = "ZZZ" := by decide +kernel
theorem colName_18279 : colName 18279 = "AAAA" := by decide +kernel

theorem colName_length_le_three {n : Nat} (h : n ≤ maxCol) : (colName n).length ≤ 3 := by
  unfold colName
  rw [String.length_ofList, List.length_map]
  exact encodeCol_length_le_three (by unfold maxCol at h; omega)

/-! ## Decimal row numbers

Rows are written in ordinary decimal. The same pattern as columns, with base 10
and a zero digit, gives a numeral with no leading zero for every positive row.
-/

def encodeDecAux : Nat → Nat → List (Fin 10)
  | 0, _ => []
  | _, 0 => []
  | k + 1, n + 1 => encodeDecAux k ((n + 1) / 10) ++ [⟨(n + 1) % 10, Nat.mod_lt _ (by decide)⟩]

/-- The decimal digits of `n`, most significant first. `0` has none. -/
def encodeDec (n : Nat) : List (Fin 10) := encodeDecAux n n

theorem encodeDecAux_fuel {k k' n : Nat} (hk : n ≤ k) (hk' : n ≤ k') :
    encodeDecAux k n = encodeDecAux k' n := by
  induction k generalizing k' n with
  | zero => obtain rfl : n = 0 := by omega
            cases k' <;> rfl
  | succ k ih =>
    match n, k' with
    | 0, 0 => rfl
    | 0, _ + 1 => rfl
    | m + 1, 0 => omega
    | m + 1, k'' + 1 =>
      simp only [encodeDecAux]
      rw [ih (by omega) (show (m + 1) / 10 ≤ k'' by omega)]

theorem encodeDec_succ (n : Nat) :
    encodeDec (n + 1) = encodeDec ((n + 1) / 10) ++ [⟨(n + 1) % 10, Nat.mod_lt _ (by decide)⟩] := by
  unfold encodeDec
  rw [encodeDecAux, encodeDecAux_fuel (k' := (n + 1) / 10) (by omega) (by omega)]

def decodeDec (ds : List (Fin 10)) : Nat := ds.foldl (fun acc d => acc * 10 + d.val) 0

theorem decodeDec_append (ds : List (Fin 10)) (d : Fin 10) :
    decodeDec (ds ++ [d]) = decodeDec ds * 10 + d.val := by
  simp [decodeDec, List.foldl_append]

theorem decodeDec_encodeDec (n : Nat) : decodeDec (encodeDec n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      rw [encodeDec_succ, decodeDec_append, ih ((n + 1) / 10) (by omega)]
      simp only
      omega

theorem encodeDec_eq_nil {n : Nat} : encodeDec n = [] ↔ n = 0 := by
  constructor
  · intro h; rw [← decodeDec_encodeDec n, h]; rfl
  · rintro rfl; rfl

def digitChar (d : Fin 10) : Char := Nat.digitChar d.val

def undigit (c : Char) : Option (Fin 10) :=
  if h : 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
    some ⟨c.toNat - 48, by omega⟩
  else none

theorem undigit_digitChar : ∀ d : Fin 10, undigit (digitChar d) = some d := by decide

theorem mapM_undigit_map_digitChar (ds : List (Fin 10)) :
    (ds.map digitChar).mapM undigit = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.mapM_cons, undigit_digitChar, ih]

/-! ## A1 references -/

/-- A cell reference, 1-based: `⟨2, 7⟩` is `B7`. -/
structure CellRef where
  col : Nat
  row : Nat
  deriving DecidableEq, Repr

/-- A reference names a real cell of a worksheet. -/
def CellRef.Valid (r : CellRef) : Prop :=
  0 < r.col ∧ r.col ≤ maxCol ∧ 0 < r.row ∧ r.row ≤ maxRow

instance (r : CellRef) : Decidable r.Valid := by unfold CellRef.Valid; infer_instance

/-- The characters of the A1 form: the column letters, then the row digits. -/
def CellRef.chars (r : CellRef) : List Char :=
  (encodeCol r.col).map letter ++ (encodeDec r.row).map digitChar

/-- The A1 form of a reference: `⟨2, 7⟩.toA1 = "B7"`. -/
def CellRef.toA1 (r : CellRef) : String := String.ofList r.chars

/-- Split off the leading capital letters. -/
def splitLetters : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if (unletter c).isSome then
      let (ls, rest) := splitLetters cs
      (c :: ls, rest)
    else ([], c :: cs)

/-- Read an A1 reference: letters, then digits, nothing else. -/
def parseA1 (s : String) : Option CellRef :=
  let (ls, ds) := splitLetters s.toList
  if ls.isEmpty || ds.isEmpty then none
  else do
    let col ← ls.mapM unletter
    let row ← ds.mapM undigit
    some ⟨decodeCol col, decodeDec row⟩

theorem splitLetters_chars (ls : List (Fin 26)) (ds : List (Fin 10)) (hd : ds ≠ []) :
    splitLetters (ls.map letter ++ ds.map digitChar) = (ls.map letter, ds.map digitChar) := by
  induction ls with
  | nil =>
    cases ds with
    | nil => contradiction
    | cons d ds => simp [splitLetters, digitChar, unletter_digitChar]
  | cons l ls ih => simp [splitLetters, unletter_letter, ih]

/-- Every valid reference reads back from its A1 form. -/
theorem parseA1_toA1 {r : CellRef} (hc : 0 < r.col) (hr : 0 < r.row) :
    parseA1 r.toA1 = some r := by
  have hl : encodeCol r.col ≠ [] := by rw [Ne, encodeCol_eq_nil]; omega
  have hd : encodeDec r.row ≠ [] := by rw [Ne, encodeDec_eq_nil]; omega
  unfold parseA1 CellRef.toA1 CellRef.chars
  rw [String.toList_ofList, splitLetters_chars _ _ hd]
  have h1 : ((encodeCol r.col).map letter).isEmpty = false := by simpa using hl
  have h2 : ((encodeDec r.row).map digitChar).isEmpty = false := by simpa using hd
  simp only [h1, h2, Bool.or_false, Bool.false_eq_true, ite_false,
    mapM_unletter_map_letter, mapM_undigit_map_digitChar]
  simp [decodeCol_encodeCol, decodeDec_encodeDec]

/-- Two different cells never share a name. -/
theorem toA1_injective {r s : CellRef} (hr : r.Valid) (hs : s.Valid)
    (h : r.toA1 = s.toA1) : r = s := by
  have := congrArg parseA1 h
  rwa [parseA1_toA1 hr.1 hr.2.2.1, parseA1_toA1 hs.1 hs.2.2.1, Option.some.injEq] at this

theorem toA1_B7 : (CellRef.mk 2 7).toA1 = "B7" := by decide +kernel
/-- The bottom-right cell of every worksheet. -/
theorem toA1_last : (CellRef.mk maxCol maxRow).toA1 = "XFD1048576" := by decide +kernel
theorem parseA1_last : parseA1 "XFD1048576" = some ⟨maxCol, maxRow⟩ := by decide +kernel

end Xlsx
