import Xlsx.CellRef

/-!
# Merged ranges, checked fast

The rules say no two merged ranges overlap, and no value sits under a merge except in its
top-left cell. Checked pair by pair, that is quadratic: Apache POI's `57893-many-merges.xlsx`
has 50,000 merges and 140,000 cells, which is 1.25 billion pairs of merges and 7 billion
merge-cell pairs, and took 115 seconds.

The fast check lists every merged cell, sorts the list, and looks for a cell twice. Two merges
overlap exactly when some cell is in both, so a list with no repeats means no overlap. The
same trick on the hidden cells (every merged cell but the top-left) and the cells holding
values finds a value under a merge. `mergesFast_sound` proves both.
-/

namespace Xlsx

/-- Reading order: by row, then by column. -/
def CellRef.lt (a b : CellRef) : Bool := a.row < b.row || (a.row == b.row && a.col < b.col)

theorem CellRef.lt_trans {a b c : CellRef} (h1 : a.lt b = true) (h2 : b.lt c = true) : a.lt c = true := by
  simp only [CellRef.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  omega

theorem CellRef.ne_of_lt {a b : CellRef} (h : a.lt b = true) : a ≠ b := by
  rintro rfl
  simp only [CellRef.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

/-- Each cell strictly after the one before. -/
def strictlySorted : List CellRef → Bool
  | a :: b :: rest => a.lt b && strictlySorted (b :: rest)
  | _ => true

theorem strictlySorted_pairwise : ∀ {l : List CellRef}, strictlySorted l = true →
    l.Pairwise (fun a b => a.lt b = true)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [strictlySorted, Bool.and_eq_true] at h
    have ih := strictlySorted_pairwise h.2
    refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact CellRef.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

/-- No cell twice: sort, then compare neighbors. -/
def noRepeats (l : List CellRef) : Bool :=
  strictlySorted (l.mergeSort fun a b => !b.lt a)

theorem noRepeats_sound {l : List CellRef} (h : noRepeats l = true) : l.Nodup := by
  have hs := (strictlySorted_pairwise h).imp fun hab => CellRef.ne_of_lt hab
  exact (List.mergeSort_perm l _).nodup_iff.1 hs

/-- Every cell of a range, row by row. -/
def Range.cells (r : Range) : List CellRef :=
  (List.range' r.first.row (r.last.row + 1 - r.first.row)).flatMap fun row =>
    (List.range' r.first.col (r.last.col + 1 - r.first.col)).map fun col => ⟨col, row⟩

theorem Range.mem_cells {r : Range} {c : CellRef} (h : r.contains c = true) : c ∈ r.cells := by
  obtain ⟨col, row⟩ := c
  simp only [Range.contains, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Range.cells, List.mem_flatMap, List.mem_map, List.mem_range']
  exact ⟨row, ⟨row - r.first.row, by omega, by omega⟩, col, ⟨col - r.first.col, by omega, by omega⟩, rfl⟩

/-- How many cells the ranges cover, counted with repeats. -/
def Range.area (r : Range) : Nat := (r.last.row + 1 - r.first.row) * (r.last.col + 1 - r.first.col)

/-- The cells a merge hides: all but the top-left. -/
def Range.hidden (r : Range) : List CellRef := r.cells.filter (· != r.first)

/-- Merges, and the cells holding values: the fast check. -/
def mergesFast (ms : List Range) (values : List CellRef) : Bool :=
  noRepeats (ms.flatMap Range.cells) && noRepeats (ms.flatMap Range.hidden ++ values)

theorem mergesFast_sound {ms : List Range} {values : List CellRef} (hv : ∀ m ∈ ms, m.Valid)
    (h : mergesFast ms values = true) :
    ms.Pairwise (fun a b => a.overlaps b = false) ∧
    ∀ m ∈ ms, ∀ c ∈ values, m.contains c = true → c ≠ m.first → False := by
  simp only [mergesFast, Bool.and_eq_true] at h
  refine ⟨?_, ?_⟩
  · have hp := (List.pairwise_flatMap.1 (noRepeats_sound h.1)).2
    refine hp.imp_of_mem fun {a b} ham hbm hab => ?_
    cases ho : a.overlaps b
    · rfl
    · -- the corner where both begin is in both
      exfalso
      obtain ⟨_, _, _, _⟩ := hv a ham
      obtain ⟨_, _, _, _⟩ := hv b hbm
      simp only [Range.overlaps, Bool.and_eq_true, decide_eq_true_eq] at ho
      have ha : a.contains ⟨max a.first.col b.first.col, max a.first.row b.first.row⟩ = true := by
        simp only [Range.contains, Bool.and_eq_true, decide_eq_true_eq, Nat.max_def]
        split <;> split <;> omega
      have hb : b.contains ⟨max a.first.col b.first.col, max a.first.row b.first.row⟩ = true := by
        simp only [Range.contains, Bool.and_eq_true, decide_eq_true_eq, Nat.max_def]
        split <;> split <;> omega
      exact hab _ (Range.mem_cells ha) _ (Range.mem_cells hb) rfl
  · intro m hm c hc hin hne
    have hd := (List.nodup_append.1 (noRepeats_sound h.2)).2.2
    have hh : c ∈ ms.flatMap Range.hidden :=
      List.mem_flatMap.2 ⟨m, hm, List.mem_filter.2 ⟨Range.mem_cells hin, by simpa using hne⟩⟩
    exact hd c hh c hc rfl

end Xlsx
