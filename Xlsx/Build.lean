import Xlsx.Workbook

/-!
# From a workbook to a package

`Workbook.toPackage` lays a workbook out as the parts, content types and relationships
of a real XLSX file:

```
[Content_Types].xml
_rels/.rels                    rId1 officeDocument → xl/workbook.xml
xl/workbook.xml
xl/_rels/workbook.xml.rels     rId1..rIdN worksheets, then styles, then shared strings
xl/worksheets/sheet1.xml ... sheetN.xml
xl/styles.xml
xl/sharedStrings.xml
```

The theorem here is about **every** workbook, not an example: whatever the number of
sheets, the layout is a well-formed package (`toPackage_wellFormed`), and it follows
the SpreadsheetML rules on top of that (`toPackage_conforms`): the main document is a
workbook, and there is one worksheet relationship per sheet, each landing on a part
typed as a worksheet.
-/

namespace Xlsx

/-! ## Numerals -/

/-- `n` in decimal, with no leading zero; `numeral 0 = ""`. -/
def numeral (n : Nat) : String := String.ofList ((encodeDec n).map digitChar)

theorem digitChar_injective {a b : Fin 10} (h : digitChar a = digitChar b) : a = b := by
  have := congrArg undigit h
  rwa [undigit_digitChar, undigit_digitChar, Option.some.injEq] at this

theorem map_injective {α β} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_injective hf h.2]

theorem numeral_injective {m n : Nat} (h : numeral m = numeral n) : m = n := by
  have h1 := congrArg String.toList h
  simp only [numeral, String.toList_ofList] at h1
  have h2 := map_injective (fun a b => digitChar_injective) h1
  rw [← decodeDec_encodeDec m, ← decodeDec_encodeDec n, h2]

theorem nodup_map {α β} {f : α → β} (hf : ∀ a b, f a = f b → a = b) {l : List α}
    (h : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  exact h.imp fun hne heq => hne (hf _ _ heq)

/-! ## The layout -/

def workbookPart : PartName := ⟨["xl"], "workbook", ["xml"]⟩
def stylesPart : PartName := ⟨["xl"], "styles", ["xml"]⟩
def sstPart : PartName := ⟨["xl"], "sharedStrings", ["xml"]⟩
def sheetPart (i : Nat) : PartName := ⟨["xl", "worksheets"], "sheet" ++ numeral i, ["xml"]⟩

/-- Relationship id `rId<i>`. -/
def rid (i : Nat) : String := "rId" ++ numeral i

def relsType : String := "application/vnd.openxmlformats-package.relationships+xml"
def workbookType : String :=
  "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"
def worksheetType : String :=
  "application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"
def stylesType : String :=
  "application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"
def sstType : String :=
  "application/vnd.openxmlformats-officedocument.spreadsheetml.sharedStrings+xml"

/-- Sheet numbers `1, ..., n`. -/
def sheetNums (n : Nat) : List Nat := List.range' 1 n

/-- The relationships of `/xl/workbook.xml`: the sheets, then styles, then shared strings. -/
def workbookRels (n : Nat) : List Rel :=
  (sheetNums n).map (fun i => ⟨rid i, .worksheet, ⟨["worksheets"], "sheet" ++ numeral i, ["xml"]⟩⟩)
  ++ [⟨rid (n + 1), .styles, ⟨[], "styles", ["xml"]⟩⟩,
      ⟨rid (n + 2), .sharedStrings, ⟨[], "sharedStrings", ["xml"]⟩⟩]

/-- The package for a workbook with `n` sheets. -/
def layout (n : Nat) : Package where
  parts := [workbookPart, stylesPart, sstPart] ++ (sheetNums n).map sheetPart
  defaults := [("rels", relsType), ("xml", "application/xml")]
  overrides := [(workbookPart, workbookType), (stylesPart, stylesType), (sstPart, sstType)]
    ++ (sheetNums n).map (fun i => (sheetPart i, worksheetType))
  rels := [(.package, [⟨rid 1, .officeDocument, workbookPart⟩]),
           (.part workbookPart, workbookRels n)]

def Workbook.toPackage (wb : Workbook) : Package := layout wb.sheets.length

/-! ## It is a well-formed package, for every number of sheets -/

theorem sheetPart_injective (a b : Nat) (h : sheetPart a = sheetPart b) : a = b := by
  simp only [sheetPart, PartName.mk.injEq, true_and, and_true] at h
  exact numeral_injective ((String.append_right_inj _).1 h)

theorem rid_injective (a b : Nat) (h : rid a = rid b) : a = b :=
  numeral_injective ((String.append_right_inj _).1 h)

theorem workbookRels_ids (n : Nat) :
    (workbookRels n).map (·.id) = (List.range' 1 (n + 2)).map rid := by
  rw [← List.range'_append (m := n) (n := 2)]
  simp [workbookRels, sheetNums, Nat.add_comm 1 n]
  rfl

theorem lookup_map_const {α β γ} [DecidableEq α] {f : γ → α} {v : β} {k : α} :
    ∀ {l : List γ}, k ∈ l.map f → (l.map fun i => (f i, v)).lookup k = some v
  | [], h => by simp at h
  | a :: l, h => by
    by_cases hk : k = f a
    · subst hk; simp
    · have : (k == f a) = false := by simpa using hk
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_const (by simpa [hk] using h)

theorem contentType_sheet {n i : Nat} (hi : i ∈ sheetNums n) :
    (layout n).contentType (sheetPart i) = some worksheetType := by
  simp only [Package.contentType, layout, List.lookup, List.cons_append]
  have h1 : (sheetPart i == workbookPart) = false := by simp [sheetPart, workbookPart]
  have h2 : (sheetPart i == stylesPart) = false := by simp [sheetPart, stylesPart]
  have h3 : (sheetPart i == sstPart) = false := by simp [sheetPart, sstPart]
  simp only [h1, h2, h3, List.nil_append]
  rw [lookup_map_const (List.mem_map_of_mem hi)]
  rfl

/-- Everything named `.xml` or `.rels` has a type, from the Defaults alone. -/
theorem layout_typed_by_ext {n : Nat} {x : PartName} (h : x.ext = "xml" ∨ x.ext = "rels") :
    ((layout n).contentType x).isSome := by
  unfold Package.contentType
  cases (layout n).overrides.lookup x with
  | some _ => rfl
  | none =>
    rcases h with h | h <;> simp [layout, List.lookup, h]

theorem relsOf_workbook (n : Nat) : (layout n).relsOf (.part workbookPart) = workbookRels n := by
  have hne : (Source.part workbookPart == Source.package) = false := by decide
  simp [Package.relsOf, layout, List.lookup, hne]

theorem layout_wellFormed (n : Nat) : (layout n).WellFormed where
  names_unique := by
    simp only [Package.allParts, Package.relsParts, layout, List.map_cons, List.map_nil,
      Source.relsPart, workbookPart, stylesPart, sstPart]
    refine List.nodup_append.2 ⟨?_, by simp, ?_⟩
    · refine List.nodup_append.2 ⟨by simp, nodup_map sheetPart_injective (List.nodup_range' ..), ?_⟩
      intro a ha b hb hab
      subst hab
      simp only [List.mem_map] at hb
      obtain ⟨i, _, rfl⟩ := hb
      simp [sheetPart] at ha
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_append, List.mem_map] at ha
      rcases ha with ha | ⟨i, _, rfl⟩
      · simp at ha hb; rcases ha with rfl | rfl | rfl <;> simp at hb
      · simp [sheetPart] at hb
  typed := by
    intro x hx
    simp only [Package.allParts, Package.relsParts, layout, List.map_cons, List.map_nil,
      Source.relsPart, List.mem_append, List.mem_map, List.mem_cons] at hx
    rcases hx with (hx | ⟨i, hi, rfl⟩) | hx
    · rcases hx with rfl | rfl | rfl | hx
      · rfl
      · rfl
      · rfl
      · simp at hx
    · rw [contentType_sheet hi]; rfl
    · rcases hx with rfl | rfl | hx
      · exact layout_typed_by_ext (Or.inr rfl)
      · exact layout_typed_by_ext (Or.inr rfl)
      · simp at hx
  sources_exist := by
    intro s rs hmem x hs
    simp only [layout, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · cases hs
    · cases hs; simp [layout]
  targets_exist := by
    intro s rs hmem r hr
    simp only [layout, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hr; subst hr; simp [layout, PartName.under, Source.dir, workbookPart]
    · simp only [workbookRels, List.mem_append, List.mem_map, List.mem_cons] at hr
      rcases hr with ⟨i, hi, rfl⟩ | rfl | rfl | hr
      · simp only [layout, List.mem_append, List.mem_map]
        exact Or.inr ⟨i, hi, rfl⟩
      · simp [layout, PartName.under, Source.dir, workbookPart, stylesPart]
      · simp [layout, PartName.under, Source.dir, workbookPart, sstPart]
      · simp at hr
  ids_unique := by
    intro s rs hmem
    simp only [layout, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp
    · rw [workbookRels_ids]
      exact nodup_map rid_injective (List.nodup_range' ..)
  one_main := by
    simp [Package.mainDocument, Package.relsOf, layout]
  reachable := by
    have hwb : (layout n).Reachable workbookPart :=
      .root ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., rfl⟩
    have hstep : ∀ r ∈ workbookRels n, (layout n).Reachable (r.target.under ["xl"]) :=
      fun r hr => .step hwb ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), r, hr, rfl⟩
    intro x hx
    simp only [layout, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
      or_false] at hx
    rcases hx with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · exact hwb
    · exact hstep ⟨rid (n + 1), .styles, ⟨[], "styles", ["xml"]⟩⟩ (by simp [workbookRels])
    · exact hstep ⟨rid (n + 2), .sharedStrings, ⟨[], "sharedStrings", ["xml"]⟩⟩
        (by simp [workbookRels])
    · exact hstep ⟨rid i, .worksheet, ⟨["worksheets"], "sheet" ++ numeral i, ["xml"]⟩⟩
        (by simp only [workbookRels, List.mem_append, List.mem_map]; exact Or.inl ⟨i, hi, rfl⟩)

/-- **Every workbook lays out as a well-formed package**, whatever its number of sheets. -/
theorem Workbook.toPackage_wellFormed (wb : Workbook) : wb.toPackage.WellFormed :=
  layout_wellFormed _

/-! ## And it follows the SpreadsheetML rules on top -/

/-- What a spreadsheet reader expects of the package, beyond the packaging rules. -/
structure SpreadsheetConforms (p : Package) (sheets : Nat) : Prop where
  /-- The main document is typed as a workbook. -/
  main_is_workbook : ∀ m ∈ p.mainDocument, p.contentType m = some workbookType
  /-- One worksheet relationship per sheet. -/
  one_rel_per_sheet :
    ((p.relsOf (.part workbookPart)).filter (·.type == .worksheet)).length = sheets
  /-- Each lands on a part typed as a worksheet. -/
  sheets_typed : ∀ r ∈ p.relsOf (.part workbookPart), r.type = .worksheet →
    p.contentType (r.target.under ["xl"]) = some worksheetType

theorem layout_conforms (n : Nat) : SpreadsheetConforms (layout n) n where
  main_is_workbook := by
    intro m hm
    simp [Package.mainDocument, Package.relsOf, layout] at hm
    subst hm; rfl
  one_rel_per_sheet := by
    rw [relsOf_workbook, workbookRels, List.filter_append]
    simp only [List.filter_map, Function.comp_def, sheetNums]
    have hw : (RelType.worksheet == RelType.worksheet) = true := rfl
    have hs : (RelType.styles == RelType.worksheet) = false := rfl
    have hsst : (RelType.sharedStrings == RelType.worksheet) = false := rfl
    simp only [hw, List.filter_cons, hs, hsst, List.filter_nil, List.length_append,
      List.length_map, Bool.false_eq_true, ite_false, List.length_nil, Nat.add_zero]
    rw [List.filter_eq_self.2 (fun _ _ => rfl), List.length_range']
  sheets_typed := by
    intro r hr ht
    rw [relsOf_workbook] at hr
    simp only [workbookRels, List.mem_append, List.mem_map, List.mem_cons] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl | rfl | hr
    · exact contentType_sheet hi
    · cases ht
    · cases ht
    · simp at hr

theorem Workbook.toPackage_conforms (wb : Workbook) :
    SpreadsheetConforms wb.toPackage wb.sheets.length :=
  layout_conforms _

end Xlsx
