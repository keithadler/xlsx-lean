import Xlsx.Build

/-!
# Tables in the layout

A table is its own part, reached from its sheet: the sheet part has a `.rels` part of
its own, whose relationships `rId1`, `rId2`, … point at the sheet's tables, and
`<tableParts>` in the sheet names them. Table `j` of sheet `i` is written as
`/xl/tables/sheet<i>/table<j>.xml`, so numbering stays local to each sheet.

`Workbook.toPackage` lays out any workbook, tables included, and the theorems of
`Build` carry over: **every workbook, with any number of sheets and tables, lays out as a
well-formed package**, follows the SpreadsheetML rules, and leaves no part unreachable.

The proofs rest on one observation: the parts this adds are the only ones three folders
deep (`xl/tables/sheetN`, and the sheets' relationships in `xl/worksheets/_rels`), and
everything the plain layout has is at most two deep. So the new names never meet the
old ones, the old parts keep their content types, and the main document is the same.
-/

namespace Xlsx

def tableType : String := "application/vnd.openxmlformats-officedocument.spreadsheetml.table+xml"
def tableRelType : String := "http://schemas.openxmlformats.org/officeDocument/2006/relationships/table"

/-- `/xl/tables/sheet<i>/table<j>.xml` -/
def tablePartOf (i j : Nat) : PartName := ⟨["xl", "tables", "sheet" ++ numeral i], "table" ++ numeral j, ["xml"]⟩

/-- The relationships of sheet `i`, which has `m` tables. -/
def sheetTableRels (i m : Nat) : List Rel :=
  (List.range' 1 m).map fun j => ⟨rid j, .other tableRelType, tablePartOf i j, true, false⟩

/-- `(sheet number, how many tables)` for each sheet. -/
def tablesOf (ts : List Nat) : List (Nat × Nat) := (sheetNums ts.length).zip ts

def tableParts (ts : List Nat) : List PartName :=
  (tablesOf ts).flatMap fun (i, m) => (List.range' 1 m).map (tablePartOf i)

def tableGroups (ts : List Nat) : List (Source × List Rel) :=
  ((tablesOf ts).filter (fun p => 0 < p.2)).map fun (i, m) => (.part (sheetPart i), sheetTableRels i m)

/-- The plain layout, plus a part per table, their Overrides, and each sheet's
relationships to its tables. -/
def layoutT (ts : List Nat) : Package :=
  let b := layout ts.length
  { b with
    parts := b.parts ++ tableParts ts
    overrides := b.overrides ++ (tableParts ts).map (·, tableType)
    rels := b.rels ++ tableGroups ts }

/-- The package for a workbook: its sheets, and each sheet's tables. -/
def Workbook.toPackage (wb : Workbook) : Package := layoutT (wb.sheets.map (·.tables.length))

/-! ## Depth -/

/-- How deep a part's folder is; `PartName.key` keeps it. -/
theorem key_depth (p : PartName) : p.key.1.length = p.dir.length := by simp [PartName.key]

theorem depth_base {n : Nat} {x : PartName} (hx : x ∈ (layout n).allParts) : x.dir.length ≤ 2 := by
  simp only [Package.allParts, Package.relsParts, layout, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false, Source.relsPart] at hx
  rcases hx with ((rfl | rfl | rfl) | ⟨i, _, rfl⟩) | (⟨_, rfl | rfl, rfl⟩) <;> simp [workbookPart, stylesPart, sstPart, sheetPart]

theorem mem_tableParts {ts : List Nat} {x : PartName} :
    x ∈ tableParts ts ↔ ∃ i m, (i, m) ∈ tablesOf ts ∧ ∃ j ∈ List.range' 1 m, tablePartOf i j = x := by
  simp [tableParts]

theorem depth_table {ts : List Nat} {x : PartName} (hx : x ∈ tableParts ts) :
    x.dir.length = 3 ∧ x.dir[1]? = some "tables" := by
  obtain ⟨i, m, _, j, _, rfl⟩ := mem_tableParts.1 hx
  simp [tablePartOf]

theorem group_source {ts : List Nat} {s : Source} {rs : List Rel} (h : (s, rs) ∈ tableGroups ts) :
    ∃ i m, (i, m) ∈ tablesOf ts ∧ 0 < m ∧ s = .part (sheetPart i) ∧ rs = sheetTableRels i m := by
  simp only [tableGroups, List.mem_map, List.mem_filter, Prod.mk.injEq] at h
  obtain ⟨⟨i, m⟩, ⟨hm, hpos⟩, rfl, rfl⟩ := h
  exact ⟨i, m, hm, by simpa using hpos, rfl, rfl⟩

theorem mem_tablesOf {ts : List Nat} {i m : Nat} (h : (i, m) ∈ tablesOf ts) : i ∈ sheetNums ts.length :=
  (List.of_mem_zip h).1

/-! ## What stays as it was -/

theorem contentType_layoutT_base {ts : List Nat} {x : PartName} (hx : x.dir.length ≤ 2) :
    (layoutT ts).contentType x = (layout ts.length).contentType x := by
  unfold Package.contentType
  have hnone : ((tableParts ts).map (·, tableType)).find? (·.1.key == x.key) = none := by
    rw [List.find?_eq_none]
    intro y hy hyx
    simp only [List.mem_map] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hd := (depth_table ht).1
    have := congrArg (fun k => k.1.length) (beq_iff_eq.1 hyx)
    simp only [key_depth] at this
    omega
  simp only [layoutT, List.find?_append, hnone, Option.or_none]

theorem relsOf_layoutT_package (ts : List Nat) :
    (layoutT ts).relsOf .package = (layout ts.length).relsOf .package := by
  simp [Package.relsOf, layoutT, layout, List.lookup]

theorem mainDocument_layoutT (ts : List Nat) : (layoutT ts).mainDocument = [workbookPart] := by
  rw [← mainDocument_layout ts.length]
  simp only [Package.mainDocument, relsOf_layoutT_package]

theorem relsOf_workbook_T (ts : List Nat) :
    (layoutT ts).relsOf (.part workbookPart) = workbookRels ts.length := by
  have hne : (Source.part workbookPart == Source.package) = false := by decide
  simp [Package.relsOf, layoutT, layout, List.lookup, hne]

/-- Following relationships in a package with more relationships reaches at least as much. -/
theorem Reachable.mono {p q : Package} (hsub : ∀ e ∈ p.rels, e ∈ q.rels) {x : PartName}
    (h : p.Reachable x) : q.Reachable x := by
  induction h with
  | root e =>
    obtain ⟨rs, hm, r, hr, hx, he⟩ := e
    exact .root ⟨rs, hsub _ hm, r, hr, hx, he⟩
  | step _ e ih =>
    obtain ⟨rs, hm, r, hr, hx, he⟩ := e
    exact .step ih ⟨rs, hsub _ hm, r, hr, hx, he⟩

/-! ## New names are distinct -/

theorem fold_prefix (pre : String) (hpre : pre.toList.map Char.toLower = pre.toList) (i : Nat) :
    PartName.fold (pre ++ numeral i) = pre.toList ++ (encodeDec i).map digitChar := by
  simp only [PartName.fold, numeral, String.toList_append, String.toList_ofList, List.map_append,
    List.map_map, hpre]
  congr 1
  exact List.map_congr_left (fun d _ => toLower_digitChar d)

theorem numeral_of_fold {pre : String} (hpre : pre.toList.map Char.toLower = pre.toList) {i j : Nat}
    (h : PartName.fold (pre ++ numeral i) = PartName.fold (pre ++ numeral j)) : i = j := by
  rw [fold_prefix pre hpre, fold_prefix pre hpre] at h
  have h2 := map_injective (fun _ _ => digitChar_injective) (List.append_cancel_left h)
  rw [← decodeDec_encodeDec i, ← decodeDec_encodeDec j, h2]

theorem sheet_lower : "sheet".toList.map Char.toLower = "sheet".toList := by decide +kernel
theorem table_lower : "table".toList.map Char.toLower = "table".toList := by decide +kernel

theorem tablePartOf_key_injective {i j i' j' : Nat}
    (h : (tablePartOf i j).key = (tablePartOf i' j').key) : i = i' ∧ j = j' := by
  simp only [PartName.key, tablePartOf, List.map_cons, List.map_nil, Prod.mk.injEq, List.cons.injEq] at h
  exact ⟨numeral_of_fold sheet_lower h.1.2.2.1, numeral_of_fold table_lower h.2.1⟩

/-- `(sheet, table)` for every table. -/
def tablePairs (ts : List Nat) : List (Nat × Nat) :=
  (tablesOf ts).flatMap fun (i, m) => (List.range' 1 m).map (i, ·)

theorem tableParts_eq (ts : List Nat) :
    tableParts ts = (tablePairs ts).map fun (i, j) => tablePartOf i j := by
  simp [tableParts, tablePairs, List.map_flatMap, Function.comp_def]

theorem firsts_tablesOf (ts : List Nat) : (tablesOf ts).map (·.1) = sheetNums ts.length := by
  simp [tablesOf, sheetNums, List.map_fst_zip]

theorem nodup_pairs : ∀ {l : List (Nat × Nat)}, (l.map (·.1)).Nodup →
    (l.flatMap fun (i, m) => (List.range' 1 m).map (i, ·)).Nodup
  | [], _ => List.nodup_nil
  | (i, m) :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.flatMap_cons]
    refine List.nodup_append.2 ⟨nodup_map (fun a b hab => by simpa using hab) (List.nodup_range' ..),
      nodup_pairs h.2, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_map] at ha
    obtain ⟨j, _, rfl⟩ := ha
    simp only [List.mem_flatMap, List.mem_map] at hb
    obtain ⟨⟨i', m'⟩, hi', j', _, he⟩ := hb
    simp only [Prod.mk.injEq] at he
    apply h.1
    rw [← he.1]
    exact List.mem_map_of_mem (f := (·.1)) hi'

theorem tableParts_keys_nodup (ts : List Nat) : ((tableParts ts).map PartName.key).Nodup := by
  rw [tableParts_eq, List.map_map]
  refine nodup_map (f := PartName.key ∘ fun (p : Nat × Nat) => tablePartOf p.1 p.2) ?_
    (nodup_pairs (by rw [firsts_tablesOf]; exact List.nodup_range' ..))
  intro a b hab
  obtain ⟨h1, h2⟩ := tablePartOf_key_injective hab
  exact Prod.ext h1 h2

theorem groupRels_keys_nodup (ts : List Nat) :
    ((tableGroups ts).map (fun g => g.1.relsPart.key)).Nodup := by
  have hf : (((tablesOf ts).filter (fun p => 0 < p.2)).map (·.1)).Nodup :=
    (List.Nodup.sublist (List.Sublist.map _ List.filter_sublist)
      (by rw [firsts_tablesOf]; exact List.nodup_range' ..))
  have : (tableGroups ts).map (fun g => g.1.relsPart.key)
      = (((tablesOf ts).filter (fun p => 0 < p.2)).map (·.1)).map
          (fun i => (Source.part (sheetPart i)).relsPart.key) := by
    simp [tableGroups, List.map_map, Function.comp_def]
  rw [this]
  refine nodup_map ?_ hf
  intro a b hab
  simp only [Source.relsPart, PartName.key, sheetPart, Prod.mk.injEq] at hab
  exact numeral_of_fold sheet_lower hab.2.1

/-! ## The layout with tables is well-formed -/

theorem Package.has_mono {p q : Package} {n : PartName} (h : p.has n) (hsub : ∀ x ∈ p.parts, x ∈ q.parts) :
    q.has n := by
  obtain ⟨x, hx, hk⟩ := h
  exact ⟨x, hsub x hx, hk⟩

theorem allParts_layoutT (ts : List Nat) : (layoutT ts).allParts =
    ((layout ts.length).parts ++ tableParts ts)
      ++ ((layout ts.length).relsParts ++ (tableGroups ts).map (·.1.relsPart)) := by
  simp [Package.allParts, Package.relsParts, layoutT]

theorem mem_group_relsPart {ts : List Nat} {x : PartName}
    (hx : x ∈ (tableGroups ts).map (·.1.relsPart)) :
    x.dir.length = 3 ∧ x.dir[1]? = some "worksheets" ∧ x.ext = "rels" := by
  simp only [List.mem_map] at hx
  obtain ⟨⟨s, rs⟩, hg, rfl⟩ := hx
  obtain ⟨i, m, _, _, rfl, rfl⟩ := group_source hg
  simp [Source.relsPart, sheetPart, PartName.ext]

theorem sheetPart_mem_layout {n i : Nat} (hi : i ∈ sheetNums n) : sheetPart i ∈ (layout n).parts := by
  simp only [layout, List.mem_append, List.mem_map]
  exact Or.inr ⟨i, hi, rfl⟩

theorem layoutT_wellFormed (ts : List Nat) : (layoutT ts).WellFormed := by
  have hb := layout_wellFormed ts.length
  have hsub : ∀ x ∈ (layout ts.length).parts, x ∈ (layoutT ts).parts := fun x hx => by
    simp [layoutT, hx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- names_unique
    rw [allParts_layoutT]
    have hbase := hb.names_unique
    simp only [Package.allParts, List.map_append] at hbase
    obtain ⟨hA, hC, hAC⟩ := List.nodup_append.1 hbase
    have hB := tableParts_keys_nodup ts
    have hD : (((tableGroups ts).map (·.1.relsPart)).map PartName.key).Nodup := by
      rw [List.map_map]; exact groupRels_keys_nodup ts
    have dAC : ∀ x ∈ (layout ts.length).allParts, x.key.1.length ≤ 2 := fun x hx => by
      rw [key_depth]; exact depth_base hx
    have dB : ∀ x ∈ tableParts ts, x.key.1.length = 3 ∧ x.key.1[1]? = some (PartName.fold "tables") := by
      intro x hx
      obtain ⟨h1, h2⟩ := depth_table hx
      refine ⟨by rw [key_depth]; exact h1, ?_⟩
      simp [PartName.key, h2]
    have dD : ∀ x ∈ (tableGroups ts).map (·.1.relsPart),
        x.key.1.length = 3 ∧ x.key.1[1]? = some (PartName.fold "worksheets") := by
      intro x hx
      obtain ⟨h1, h2, _⟩ := mem_group_relsPart hx
      refine ⟨by rw [key_depth]; exact h1, ?_⟩
      simp [PartName.key, h2]
    have htw : PartName.fold "tables" ≠ PartName.fold "worksheets" := by decide +kernel
    simp only [List.map_append]
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hA, hB, ?_⟩, List.nodup_append.2 ⟨hC, hD, ?_⟩, ?_⟩
    · intro a ha b hb' hab; subst hab
      simp only [List.mem_map] at ha hb'
      obtain ⟨x, hx, rfl⟩ := ha; obtain ⟨y, hy, hxy⟩ := hb'
      have := dAC x (by simp [Package.allParts, hx]); rw [← hxy, (dB y hy).1] at this; omega
    · intro a ha b hb' hab; subst hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha; obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hb'
      have := dAC x (by simp [Package.allParts, hx]); rw [← hxy, (dD y hy).1] at this; omega
    · intro a ha b hb' hab; subst hab
      simp only [List.mem_append] at ha hb'
      have lenB : ∀ y ∈ (tableGroups ts).map (·.1.relsPart), y.key.1.length = 3 := fun y hy => (dD y hy).1
      rcases ha with ha | ha <;> rcases hb' with hb' | hb'
      · exact hAC _ ha _ hb' rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hb'
        have := dAC x (by simp [Package.allParts, hx]); rw [← hxy, lenB y hy] at this; omega
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hb'
        have := dAC y (by simp [Package.allParts, hy]); rw [hxy, (dB x hx).1] at this; omega
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
        obtain ⟨y, hy, hxy⟩ := List.mem_map.1 hb'
        have h1 := (dB x hx).2; have h2 := (dD y hy).2
        rw [hxy, h1] at h2
        exact htw (Option.some.inj h2)
  · -- typed
    intro x hx
    rw [allParts_layoutT] at hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · rw [contentType_layoutT_base (depth_base (n := ts.length) (by simp [Package.allParts, hx]))]
      exact hb.typed x (by simp [Package.allParts, hx])
    · unfold Package.contentType
      have : ((layoutT ts).overrides.find? (·.1.key == x.key)).isSome := by
        rw [List.find?_isSome]
        exact ⟨(x, tableType), by simp [layoutT, hx], by simp⟩
      cases h : (layoutT ts).overrides.find? (·.1.key == x.key) with
      | some _ => rfl
      | none => rw [h] at this; cases this
    · rw [contentType_layoutT_base (depth_base (n := ts.length) (by simp [Package.allParts, hx]))]
      exact hb.typed x (by simp [Package.allParts, hx])
    · have hext := (mem_group_relsPart hx).2.2
      unfold Package.contentType
      cases ((layoutT ts).overrides.find? (·.1.key == x.key)).map (·.2) with
      | some _ => rfl
      | none =>
        have e : (layoutT ts).defaults = [("rels", relsType), ("xml", "application/xml")] := rfl
        rw [e, hext]; decide +kernel
  · -- sources_exist
    intro s rs hmem n hs
    simp only [layoutT, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Package.has_mono (hb.sources_exist s rs hmem n hs) hsub
    · obtain ⟨i, m, him, _, rfl, rfl⟩ := group_source hmem
      cases hs
      exact Package.has_of_mem (hsub _ (sheetPart_mem_layout (mem_tablesOf him)))
  · -- targets_exist
    intro s rs hmem r hr hx
    simp only [layoutT, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Package.has_mono (hb.targets_exist s rs hmem r hr hx) hsub
    · obtain ⟨i, m, him, _, rfl, rfl⟩ := group_source hmem
      simp only [sheetTableRels, List.mem_map] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      apply Package.has_of_mem
      simp only [layoutT, List.mem_append, Rel.resolve, ite_true]
      exact Or.inr (mem_tableParts.2 ⟨i, m, him, j, hj, rfl⟩)
  · -- ids_unique
    intro s rs hmem
    simp only [layoutT, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact hb.ids_unique s rs hmem
    · obtain ⟨i, m, _, _, rfl, rfl⟩ := group_source hmem
      simp only [sheetTableRels, List.map_map, Function.comp_def]
      exact nodup_map rid_injective (List.nodup_range' ..)
  · -- one_main
    rw [mainDocument_layoutT]; rfl

/-! ## Every table can be found, and the SpreadsheetML rules still hold -/

theorem rels_layoutT_sub (ts : List Nat) : ∀ e ∈ (layout ts.length).rels, e ∈ (layoutT ts).rels :=
  fun e he => by simp [layoutT, he]

theorem layout_reach_workbook (n : Nat) : (layout n).Reachable workbookPart :=
  .root ⟨_, List.mem_cons_self .., _, List.mem_cons_self .., rfl, rfl⟩

theorem layout_reach_sheet {n i : Nat} (hi : i ∈ sheetNums n) : (layout n).Reachable (sheetPart i) :=
  .step (layout_reach_workbook n)
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
      ⟨rid i, .worksheet, ⟨["worksheets"], "sheet" ++ numeral i, ["xml"]⟩, false, false⟩,
      by simp only [workbookRels, List.mem_append, List.mem_map]; exact Or.inl ⟨i, hi, rfl⟩, rfl, rfl⟩

theorem layoutT_noOrphans (ts : List Nat) : (layoutT ts).NoOrphans := by
  intro x hx
  simp only [layoutT, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨m, hm, hk⟩ := layout_noOrphans ts.length x hx
    exact ⟨m, Reachable.mono (rels_layoutT_sub ts) hm, hk⟩
  · obtain ⟨i, m, him, j, hj, rfl⟩ := mem_tableParts.1 hx
    have hpos : 0 < m := by simp at hj; omega
    refine ⟨tablePartOf i j, .step (Reachable.mono (rels_layoutT_sub ts) (layout_reach_sheet (mem_tablesOf him)))
      ⟨sheetTableRels i m, ?_, ⟨rid j, .other tableRelType, tablePartOf i j, true, false⟩, ?_, rfl, rfl⟩, rfl⟩
    · simp only [layoutT, List.mem_append, tableGroups, List.mem_map, List.mem_filter]
      exact Or.inr ⟨(i, m), ⟨him, by simpa using hpos⟩, rfl⟩
    · simp only [sheetTableRels, List.mem_map]
      exact ⟨j, hj, rfl⟩

theorem layoutT_conforms (ts : List Nat) : SpreadsheetConforms (layoutT ts) ts.length where
  main_is_workbook := by
    intro m hm
    rw [mainDocument_layoutT] at hm
    simp at hm; subst hm
    rw [contentType_layoutT_base (by simp [workbookPart])]
    exact (layout_conforms ts.length).main_is_workbook workbookPart (by rw [mainDocument_layout]; simp)
  one_rel_per_sheet := by
    intro m hm
    rw [mainDocument_layoutT] at hm
    simp at hm; subst hm
    rw [relsOf_workbook_T, ← relsOf_workbook]
    exact (layout_conforms ts.length).one_rel_per_sheet workbookPart (by rw [mainDocument_layout]; simp)
  sheets_typed := by
    intro m hm r hr ht
    rw [mainDocument_layoutT] at hm
    simp at hm; subst hm
    rw [relsOf_workbook_T] at hr
    have hd : (r.resolve workbookPart.dir).dir.length ≤ 2 := by
      simp only [workbookRels, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨i, _, rfl⟩ | rfl | rfl <;> simp [Rel.resolve, PartName.under, workbookPart]
    rw [contentType_layoutT_base hd]
    exact (layout_conforms ts.length).sheets_typed workbookPart (by rw [mainDocument_layout]; simp) r
      (by rw [relsOf_workbook]; exact hr) ht

/-- **Every workbook lays out as a well-formed package**, whatever its number of sheets and
tables. -/
theorem Workbook.toPackage_wellFormed (wb : Workbook) : wb.toPackage.WellFormed :=
  layoutT_wellFormed _

/-- And every part, tables included, is found from the package. -/
theorem Workbook.toPackage_noOrphans (wb : Workbook) : wb.toPackage.NoOrphans :=
  layoutT_noOrphans _

/-- And the SpreadsheetML rules hold: the main document is a workbook, with one
worksheet relationship per sheet, each landing on a part typed as a worksheet. -/
theorem Workbook.toPackage_conforms (wb : Workbook) :
    SpreadsheetConforms wb.toPackage wb.sheets.length := by
  have := layoutT_conforms (wb.sheets.map (·.tables.length))
  simpa [Workbook.toPackage] using this

end Xlsx
