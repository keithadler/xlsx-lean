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
  (sheetNums n).map (fun i => ⟨rid i, .worksheet, ⟨["worksheets"], "sheet" ++ numeral i, ["xml"]⟩, false, false⟩)
  ++ [⟨rid (n + 1), .styles, ⟨[], "styles", ["xml"]⟩, false, false⟩,
      ⟨rid (n + 2), .sharedStrings, ⟨[], "sharedStrings", ["xml"]⟩, false, false⟩]

/-- The package for a workbook with `n` sheets. -/
def layout (n : Nat) : Package where
  parts := [workbookPart, stylesPart, sstPart] ++ (sheetNums n).map sheetPart
  defaults := [("rels", relsType), ("xml", "application/xml")]
  overrides := [(workbookPart, workbookType), (stylesPart, stylesType), (sstPart, sstType)]
    ++ (sheetNums n).map (fun i => (sheetPart i, worksheetType))
  rels := [(.package, [⟨rid 1, .officeDocument, workbookPart, false, false⟩]),
           (.part workbookPart, workbookRels n)]

/-! ## It is a well-formed package, for every number of sheets -/

theorem toLower_digitChar : ∀ d : Fin 10, (digitChar d).toLower = digitChar d := by decide

theorem fold_sheet (i : Nat) :
    PartName.fold ("sheet" ++ numeral i) = "sheet".toList ++ (encodeDec i).map digitChar := by
  simp only [PartName.fold, numeral, String.toList_append, String.toList_ofList, List.map_append,
    List.map_map]
  have hs : "sheet".toList.map Char.toLower = "sheet".toList := by decide +kernel
  rw [hs]
  congr 1
  exact List.map_congr_left (fun d _ => toLower_digitChar d)

/-- Sheet part names stay distinct when compared without case. -/
theorem sheetKey_injective (a b : Nat) (h : (sheetPart a).key = (sheetPart b).key) : a = b := by
  simp only [PartName.key, sheetPart, Prod.mk.injEq] at h
  have h1 := h.2.1
  rw [fold_sheet, fold_sheet] at h1
  have h2 := map_injective (fun _ _ => digitChar_injective) (List.append_cancel_left h1)
  rw [← decodeDec_encodeDec a, ← decodeDec_encodeDec b, h2]

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

theorem find?_map_const {α β} {f : Nat → α} {v : β} {q : α × β → Bool} :
    ∀ {l : List Nat}, (∃ x ∈ l, q (f x, v) = true) →
      ((l.map fun i => (f i, v)).find? q).map (·.2) = some v
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : q (f a, v) = true
    · simp [ha]
    · simp only [List.map_cons, List.find?, Bool.not_eq_true] at ha ⊢
      rw [ha]
      obtain ⟨x, hx, hq⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [ha] at hq; cases hq
      · exact find?_map_const ⟨x, hx, hq⟩

theorem contentType_sheet {n i : Nat} (hi : i ∈ sheetNums n) :
    (layout n).contentType (sheetPart i) = some worksheetType := by
  have hd : ∀ j, (sheetPart j).key.1 = [PartName.fold "xl", PartName.fold "worksheets"] := fun _ => rfl
  have ne (p : PartName) (hp : p.key.1.length = 1) : (p.key == (sheetPart i).key) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg (fun k => k.1.length) h
    simp only [hd] at this
    rw [hp] at this
    cases this
  unfold Package.contentType
  have e : (layout n).overrides = [(workbookPart, workbookType), (stylesPart, stylesType),
      (sstPart, sstType)] ++ (sheetNums n).map (fun i => (sheetPart i, worksheetType)) := rfl
  have h3 : [(workbookPart, workbookType), (stylesPart, stylesType), (sstPart, sstType)].find?
      (·.1.key == (sheetPart i).key) = none := by
    simp only [List.find?, ne workbookPart rfl, ne stylesPart rfl, ne sstPart rfl]
  rw [e, List.find?_append, h3, Option.none_or, find?_map_const ⟨i, hi, by simp⟩]
  rfl

/-- Everything named `.xml` or `.rels` has a type, from the Defaults alone. -/
theorem layout_typed_by_ext {n : Nat} {x : PartName} (h : x.ext = "xml" ∨ x.ext = "rels") :
    ((layout n).contentType x).isSome := by
  unfold Package.contentType
  cases ((layout n).overrides.find? (·.1.key == x.key)).map (·.2) with
  | some _ => rfl
  | none =>
    have e : (layout n).defaults = [("rels", relsType), ("xml", "application/xml")] := rfl
    rcases h with h | h <;> (rw [h, e]; decide +kernel)

theorem relsOf_workbook (n : Nat) : (layout n).relsOf (.part workbookPart) = workbookRels n := by
  have hne : (Source.part workbookPart == Source.package) = false := by decide
  simp [Package.relsOf, layout, List.lookup, hne]

theorem layout_wellFormed (n : Nat) : (layout n).WellFormed where
  names_unique := by
    have e : (layout n).allParts.map PartName.key =
        ([workbookPart.key, stylesPart.key, sstPart.key] ++ (sheetNums n).map (fun i => (sheetPart i).key))
        ++ [Source.package.relsPart.key, (Source.part workbookPart).relsPart.key] := by
      simp [Package.allParts, Package.relsParts, layout, List.map_map, Function.comp_def]
    rw [e]
    have hd : ∀ i, (sheetPart i).key.1 = [PartName.fold "xl", PartName.fold "worksheets"] := fun _ => rfl
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨by decide +kernel,
      nodup_map sheetKey_injective (List.nodup_range' ..), ?_⟩, by decide +kernel, ?_⟩
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_map] at hb
      obtain ⟨i, _, hi⟩ := hb
      have := congrArg Prod.fst hi
      rw [hd] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> revert this <;> decide +kernel
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with (rfl | rfl | rfl) | ⟨i, _, rfl⟩
      all_goals first
        | (rcases hb with h | h <;> revert h <;> decide +kernel)
        | (rcases hb with h | h <;> (have := congrArg Prod.fst h; rw [hd] at this; revert this; decide +kernel))
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
    · cases hs; exact Package.has_of_mem (by simp [layout])
  targets_exist := by
    intro s rs hmem r hr _
    apply Package.has_of_mem
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

/-- And it has no orphans: every part is found from the package. -/
theorem workbookRels_internal {n : Nat} : ∀ r ∈ workbookRels n, r.external = false := by
  intro r hr
  simp only [workbookRels, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨i, _, rfl⟩ | rfl | rfl <;> rfl

theorem layout_noOrphans (n : Nat) : (layout n).NoOrphans := by
  have hwb : (layout n).Reachable workbookPart :=
    .root ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., rfl, rfl⟩
  have hstep : ∀ r ∈ workbookRels n, (layout n).Reachable (r.resolve ["xl"]) :=
    fun r hr => .step hwb ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), r, hr,
      workbookRels_internal r hr, rfl⟩
  intro x hx
  simp only [layout, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hx
  rcases hx with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · exact ⟨_, hwb, rfl⟩
  · exact ⟨_, hstep ⟨rid (n + 1), .styles, ⟨[], "styles", ["xml"]⟩, false, false⟩ (by simp [workbookRels]), rfl⟩
  · exact ⟨_, hstep ⟨rid (n + 2), .sharedStrings, ⟨[], "sharedStrings", ["xml"]⟩, false, false⟩
      (by simp [workbookRels]), rfl⟩
  · exact ⟨_, hstep ⟨rid i, .worksheet, ⟨["worksheets"], "sheet" ++ numeral i, ["xml"]⟩, false, false⟩
      (by simp only [workbookRels, List.mem_append, List.mem_map]; exact Or.inl ⟨i, hi, rfl⟩), rfl⟩

/-! ## And it follows the SpreadsheetML rules on top -/

theorem mainDocument_layout (n : Nat) : (layout n).mainDocument = [workbookPart] := by
  simp [Package.mainDocument, Package.relsOf, layout]
  rfl

/-- What a spreadsheet reader expects of the package, beyond the packaging rules. It
follows the main document wherever it is, as a reader does; it does not assume
`/xl/workbook.xml`. -/
structure SpreadsheetConforms (p : Package) (sheets : Nat) : Prop where
  /-- The main document is typed as a workbook. -/
  main_is_workbook : ∀ m ∈ p.mainDocument, p.contentType m = some workbookType
  /-- One worksheet relationship per sheet. -/
  one_rel_per_sheet : ∀ m ∈ p.mainDocument,
    ((p.relsOf (.part m)).filter (·.type == .worksheet)).length = sheets
  /-- Each lands on a part typed as a worksheet. -/
  sheets_typed : ∀ m ∈ p.mainDocument, ∀ r ∈ p.relsOf (.part m), r.type = .worksheet →
    p.contentType (r.resolve m.dir) = some worksheetType

/-- The SpreadsheetML rules, as a check that runs. -/
def conformsCheck (p : Package) (sheets : Nat) : Bool :=
  p.mainDocument.all fun m =>
    p.contentType m == some workbookType
    && ((p.relsOf (.part m)).filter (·.type == .worksheet)).length == sheets
    && (p.relsOf (.part m)).all fun r =>
        r.type != .worksheet || p.contentType (r.resolve m.dir) == some worksheetType

theorem conformsCheck_sound {p : Package} {n : Nat} (h : conformsCheck p n = true) :
    SpreadsheetConforms p n := by
  simp only [conformsCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    bne_iff_ne, ne_eq] at h
  refine ⟨fun m hm => (h m hm).1.1, fun m hm => (h m hm).1.2, ?_⟩
  intro m hm r hr ht
  rcases (h m hm).2 r hr with h' | h'
  · exact absurd ht h'
  · exact h'

theorem layout_conforms (n : Nat) : SpreadsheetConforms (layout n) n where
  main_is_workbook := by
    intro m hm
    rw [mainDocument_layout] at hm
    simp at hm; subst hm; rfl
  one_rel_per_sheet := by
    intro m hm
    rw [mainDocument_layout] at hm
    simp at hm; subst hm
    rw [relsOf_workbook, workbookRels, List.filter_append]
    simp only [List.filter_map, Function.comp_def, sheetNums]
    have hw : (RelType.worksheet == RelType.worksheet) = true := rfl
    have hs : (RelType.styles == RelType.worksheet) = false := rfl
    have hsst : (RelType.sharedStrings == RelType.worksheet) = false := rfl
    simp only [hw, List.filter_cons, hs, hsst, List.filter_nil, List.length_append,
      List.length_map, Bool.false_eq_true, ite_false, List.length_nil, Nat.add_zero]
    rw [List.filter_eq_self.2 (fun _ _ => rfl), List.length_range']
  sheets_typed := by
    intro m hm r hr ht
    rw [mainDocument_layout] at hm
    simp at hm; subst hm
    rw [relsOf_workbook] at hr
    simp only [workbookRels, List.mem_append, List.mem_map, List.mem_cons] at hr
    rcases hr with ⟨i, hi, rfl⟩ | rfl | rfl | hr
    · exact contentType_sheet hi
    · cases ht
    · cases ht
    · simp at hr


end Xlsx
