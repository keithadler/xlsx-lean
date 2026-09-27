import Xlsx.Xml

/-!
# An example workbook, checked

Two sheets. `Limits` states the facts this project proves, with the theorem that proves
each. `Columns` is computed: each row holds a column number and `colName` of it.

`example_wellFormed` is checked by the kernel running `Workbook.check`, not by
`native_decide`, so it rests on no extra axiom.
-/

namespace Xlsx.Example

def sst : List String :=
  [ "Fact", "Value", "Proved by"                                      -- 0 1 2
  , "Last column", "Its name", "Last row", "Last cell"                -- 3 4 5 6
  , "Every workbook lays out as a well-formed package"                -- 7
  , "colName_maxCol", "maxRow_eq", "toA1_last"                        -- 8 9 10
  , "Workbook.toPackage_wellFormed", "Column", "Name" ]                -- 11 12 13

def txt (col row i : Nat) (style := 0) : Cell := ⟨⟨col, row⟩, .shared i, style⟩
def num (col row : Nat) (n : Int) : Cell := ⟨⟨col, row⟩, .number n, 0⟩
def str (col row : Nat) (s : String) : Cell := ⟨⟨col, row⟩, .inline s, 0⟩

def limits : Sheet where
  name := "Limits"
  rows :=
    [ ⟨1, [txt 1 1 0 1, txt 2 1 1 1, txt 3 1 2 1]⟩
    , ⟨2, [txt 1 2 3, num 2 2 16384, txt 3 2 8]⟩
    , ⟨3, [txt 1 3 4, str 2 3 (colName maxCol), txt 3 3 8]⟩
    , ⟨4, [txt 1 4 5, num 2 4 1048576, txt 3 4 9]⟩
    , ⟨5, [txt 1 5 6, str 2 5 (CellRef.mk maxCol maxRow).toA1, txt 3 5 10]⟩
    , ⟨6, [txt 1 6 7, ⟨⟨2, 6⟩, .bool true, 0⟩, txt 3 6 11]⟩ ]

def sampleColumns : List Nat := [1, 2, 26, 27, 28, 52, 53, 702, 703, 16384]

def columns : Sheet where
  name := "Columns"
  rows := ⟨1, [txt 1 1 12 1, txt 2 1 13 1]⟩ ::
    (sampleColumns.zip (List.range' 2 sampleColumns.length)).map fun (n, r) =>
      ⟨r, [num 1 r n, str 2 r (colName n)]⟩

def workbook : Workbook where
  sheets := [limits, columns]
  sst := sst
  styleCount := 2

/-- The example follows every workbook rule, checked by the kernel. -/
theorem example_wellFormed : workbook.WellFormed :=
  Workbook.check_sound (by decide +kernel)

/-- Its package, checked by running the package checker too. This one needs no general
theorem: it is the same fact `Workbook.toPackage_wellFormed` gives, found a second way. -/
theorem example_package_checks : workbook.toPackage.check = true := by decide +kernel

theorem example_package_wellFormed : workbook.toPackage.WellFormed :=
  Workbook.toPackage_wellFormed workbook

/-- What a reader sees at `Limits!B3`. -/
theorem limits_B3 : limits.value sst ⟨2, 3⟩ = some (.text "XFD") := by decide +kernel

/-- `Limits!A1` is stored as shared string 0, and reads as `Fact`. -/
theorem limits_A1 : limits.value sst ⟨1, 1⟩ = some (.text "Fact") := by decide +kernel

end Xlsx.Example
