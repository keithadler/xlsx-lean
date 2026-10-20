/-!
# What an edit left alone

An editor that changes one cell has no business touching the rest of the file. This is that promise as a check
between two archives: given the parts before, the parts after, and the parts the edit is allowed to change,
`damaged` names every part that was changed, added or removed without permission.

`damaged_empty_kept` and `damaged_empty_added` are what an empty answer means: every part the edit was not allowed
to touch is in the new file with exactly the same bytes, and the new file has no part the old one lacked outside
the allowed set. `damaged_self` says a file is always preserved against itself.

Parts are compared after decompression, so a different compression level for the same bytes is not a change.
-/

namespace Xlsx.Preserved

/-- A part name with its bytes. -/
abbrev Parts := List (String × List UInt8)

/-- Parts that changed or went missing, then parts that appeared, where `allow` does not cover the name. -/
def damaged (allow : String → Bool) (before after : Parts) : List String :=
  (before.filter fun p => !allow p.1 && !after.contains p).map (·.1) ++
  (after.filter fun q => !allow q.1 && !before.any fun p => p.1 == q.1).map (·.1)

theorem damaged_empty_kept {allow : String → Bool} {before after : Parts}
    (h : damaged allow before after = []) :
    ∀ p ∈ before, allow p.1 = false → p ∈ after := by
  intro p hp ha
  have h1 := (List.append_eq_nil_iff.mp h).1
  have h2 := List.map_eq_nil_iff.mp h1
  have := List.filter_eq_nil_iff.mp h2 p hp
  simp [ha] at this
  exact this

theorem damaged_empty_added {allow : String → Bool} {before after : Parts}
    (h : damaged allow before after = []) :
    ∀ q ∈ after, allow q.1 = false → ∃ p ∈ before, p.1 = q.1 := by
  intro q hq ha
  have h1 := (List.append_eq_nil_iff.mp h).2
  have h2 := List.map_eq_nil_iff.mp h1
  have := List.filter_eq_nil_iff.mp h2 q hq
  simp [ha] at this
  obtain ⟨d, hm⟩ := this
  exact ⟨(q.1, d), hm, rfl⟩

theorem damaged_self (allow : String → Bool) (parts : Parts) : damaged allow parts parts = [] := by
  unfold damaged
  have h1 : (parts.filter fun p => !allow p.1 && !parts.contains p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp [hp]
  have h2 : (parts.filter fun q => !allow q.1 && !parts.any fun p => p.1 == q.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro q hq
    have : (parts.any fun p => p.1 == q.1) = true := List.any_eq_true.mpr ⟨q, hq, by simp⟩
    simp [this]
  rw [h1, h2]
  rfl

end Xlsx.Preserved
