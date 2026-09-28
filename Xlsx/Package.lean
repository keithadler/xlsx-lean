import Xlsx.CellRef

/-!
# The package: Open Packaging Conventions

An XLSX file is a ZIP archive, and the archive is a *package* (ECMA-376 Part 2):

* **parts**, files with names like `/xl/workbook.xml`;
* **`[Content_Types].xml`**, which gives every part a content type, either by its
  extension (a *Default*) or by its exact name (an *Override*);
* **relationships**: each part that points at others has a `_rels/<name>.rels` part
  beside it, listing targets by id and type. The package itself has `/_rels/.rels`,
  whose `officeDocument` relationship says where the workbook is.

A reader finds everything by following relationships from the package, never by
guessing file names. So a package is only usable when every relationship lands on a
part that exists, every part has a content type, and every part can be reached.

This file models that, defines the rules as a `Prop`, writes a checker that runs,
and proves the checker sound.

Part names are kept as structure rather than text (a folder path, a stem and a chain
of extensions), so that "the relationships part of `/xl/workbook.xml` is
`/xl/_rels/workbook.xml.rels`" is a definition instead of string surgery.
Relationship targets are relative to the source's folder, as in real files; `..`
is not modeled.
-/

namespace Xlsx

/-- A part name: `/xl/worksheets/sheet1.xml` is `⟨["xl", "worksheets"], "sheet1", ["xml"]⟩`. -/
structure PartName where
  dir : List String
  stem : String
  exts : List String
  deriving DecidableEq, Repr

namespace PartName

/-- The extension a Default content type is matched on: the last one. -/
def ext (p : PartName) : String := p.exts.getLast?.getD ""

/-- The name as it appears in the ZIP archive and in `[Content_Types].xml`. -/
def render (p : PartName) : String :=
  "/" ++ String.join (p.dir.map (· ++ "/")) ++ p.stem ++ String.join (p.exts.map ("." ++ ·))

/-- ASCII case folding. OPC compares part names without regard to ASCII case
(ECMA-376 Part 2, §6.2.2.3), so `/xl/Workbook.xml` and `/xl/workbook.xml` are one name. -/
def fold (s : String) : List Char := s.toList.map Char.toLower

/-- What two part names are compared by. -/
def key (p : PartName) : List (List Char) × List Char × List (List Char) :=
  (p.dir.map fold, fold p.stem, p.exts.map fold)

/-- A relative target resolved against the folder of a source part. -/
def under (dir : List String) (t : PartName) : PartName := { t with dir := dir ++ t.dir }

end PartName

/-- Where relationships come from: the package itself, or a part. -/
inductive Source where
  | package
  | part (p : PartName)
  deriving DecidableEq, Repr

namespace Source

/-- The folder relative targets are resolved against. -/
def dir : Source → List String
  | .package => []
  | .part p => p.dir

/-- The part holding this source's relationships: `/_rels/.rels` for the package,
`/xl/_rels/workbook.xml.rels` for `/xl/workbook.xml`. -/
def relsPart : Source → PartName
  | .package => ⟨["_rels"], "", ["rels"]⟩
  | .part p => ⟨p.dir ++ ["_rels"], p.stem, p.exts ++ ["rels"]⟩

end Source

/-- The kinds of relationship an XLSX package uses. -/
inductive RelType where
  | officeDocument
  | coreProperties
  | extendedProperties
  | worksheet
  | sharedStrings
  | styles
  | theme
  /-- Any other relationship type, by its URI: calcChain, drawings, printer settings… -/
  | other (uri : String)
  deriving DecidableEq, Repr

/-- The URI each relationship type is written as. -/
def RelType.uri : RelType → String
  | .officeDocument =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument"
  | .coreProperties =>
    "http://schemas.openxmlformats.org/package/2006/relationships/metadata/core-properties"
  | .extendedProperties =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/extended-properties"
  | .worksheet =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet"
  | .sharedStrings =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/sharedStrings"
  | .styles =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles"
  | .theme =>
    "http://schemas.openxmlformats.org/officeDocument/2006/relationships/theme"
  | .other u => u

/-- One relationship: `<Relationship Id="rId1" Type="..." Target="worksheets/sheet1.xml"/>`. -/
structure Rel where
  id : String
  type : RelType
  target : PartName
  /-- `Target="/xl/workbook.xml"` (from the package root) rather than relative to the
  source's folder. openpyxl writes absolute targets; Excel writes relative ones. -/
  absolute : Bool := false
  deriving DecidableEq, Repr

/-- Where a relationship lands, seen from a source in folder `dir`. -/
def Rel.resolve (dir : List String) (r : Rel) : PartName :=
  if r.absolute then r.target else r.target.under dir

@[simp] theorem Rel.resolve_relative (dir : List String) (i : String) (t : RelType) (p : PartName) :
    (Rel.mk i t p false).resolve dir = p.under dir := rfl

/-- A package. `parts` lists the ordinary parts; the relationships parts are the
`relsPart` of each source in `rels`, and `[Content_Types].xml` is not a part at all. -/
structure Package where
  parts : List PartName
  defaults : List (String × String)
  overrides : List (PartName × String)
  rels : List (Source × List Rel)
  deriving Repr

namespace Package

/-- The relationships parts. -/
def relsParts (p : Package) : List PartName := p.rels.map (·.1.relsPart)

/-- Every entry of the archive except `[Content_Types].xml`. -/
def allParts (p : Package) : List PartName := p.parts ++ p.relsParts

/-- A part's content type: its Override if it has one, otherwise the Default for its
extension. Both are matched without regard to ASCII case, as OPC requires. -/
def contentType (p : Package) (n : PartName) : Option String :=
  ((p.overrides.find? (·.1.key == n.key)).map (·.2)).or
    ((p.defaults.find? (fun d => PartName.fold d.1 == PartName.fold n.ext)).map (·.2))

/-- The package has a part of this name, compared without regard to ASCII case: a
relationship to `sharedStrings.xml` finds `SharedStrings.xml`, as it does in Excel. -/
def has (p : Package) (n : PartName) : Prop := ∃ q ∈ p.parts, q.key = n.key

def hasB (p : Package) (n : PartName) : Bool := p.parts.any (·.key == n.key)

theorem hasB_sound {p : Package} {n : PartName} (h : p.hasB n = true) : p.has n := by
  simp only [hasB, List.any_eq_true, beq_iff_eq] at h
  exact h

theorem has_of_mem {p : Package} {n : PartName} (h : n ∈ p.parts) : p.has n := ⟨n, h, rfl⟩

/-- The relationships of one source. -/
def relsOf (p : Package) (s : Source) : List Rel := (p.rels.lookup s).getD []

/-- `a` points at `b` by some relationship. -/
def Edge (p : Package) (a : Source) (b : PartName) : Prop :=
  ∃ rs, (a, rs) ∈ p.rels ∧ ∃ r ∈ rs, r.resolve a.dir = b

/-- A part a reader can find by following relationships from the package. -/
inductive Reachable (p : Package) : PartName → Prop where
  | root {b} : p.Edge .package b → Reachable p b
  | step {a b} : Reachable p a → p.Edge (.part a) b → Reachable p b

/-- What `/_rels/.rels` names as the main document. -/
def mainDocument (p : Package) : List PartName :=
  (p.relsOf .package).filterMap fun r =>
    if r.type = .officeDocument then some (r.resolve []) else none

/-- The rules a package must follow for a reader to open it. -/
structure WellFormed (p : Package) : Prop where
  /-- No two entries of the archive have the same name, ignoring ASCII case. -/
  names_unique : (p.allParts.map PartName.key).Nodup
  /-- Every part, relationships parts included, has a content type. -/
  typed : ∀ n ∈ p.allParts, (p.contentType n).isSome
  /-- Relationships come from the package or from a part that exists. -/
  sources_exist : ∀ s rs, (s, rs) ∈ p.rels → ∀ n, s = .part n → p.has n
  /-- Every relationship lands on a part that exists. -/
  targets_exist : ∀ s rs, (s, rs) ∈ p.rels → ∀ r ∈ rs, p.has (r.resolve s.dir)
  /-- Within one `.rels` part, ids are unique. -/
  ids_unique : ∀ s rs, (s, rs) ∈ p.rels → (rs.map (·.id)).Nodup
  /-- The package names exactly one main document. -/
  one_main : p.mainDocument.length = 1

/-- A rule for *writers*, not a condition for reading: every part can be found from the
package. The standard tells readers to ignore parts they cannot place (ECMA-376 Part 1,
§9.1.4), so an orphan does not make a package unreadable; it is only untidy. It was a
`WellFormed` rule until the adversarial corpus showed that to be stricter than the
standard. -/
def NoOrphans (p : Package) : Prop := ∀ n ∈ p.parts, ∃ m, p.Reachable m ∧ m.key = n.key

/-! ## The checker -/

/-- No duplicates, as a `Bool` that runs. -/
def noDups {α} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: as => !as.contains a && noDups as

theorem noDups_sound {α} [DecidableEq α] {l : List α} (h : noDups l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [noDups, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, ih h.2⟩
    have := List.contains_iff_mem.2 hm
    rw [h.1] at this
    cases this

theorem mem_of_lookup {α β} [DecidableEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    obtain ⟨k, v⟩ := x
    by_cases hk : a = k
    · subst hk; simp [List.lookup] at h; simp [h]
    · have : (a == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Targets of relationships from any of `srcs`. -/
def targetsFrom (p : Package) (srcs : List Source) : List PartName :=
  p.rels.flatMap fun (s, rs) => if srcs.contains s then rs.map (·.resolve s.dir) else []

/-- Parts found after `k` rounds of following relationships from the package. -/
def found (p : Package) : Nat → List PartName
  | 0 => p.targetsFrom [.package]
  | k + 1 =>
    let f := p.found k
    f ++ p.targetsFrom (f.map .part)

/-- The checker. -/
def check (p : Package) : Bool :=
  noDups (p.allParts.map PartName.key)
  && p.allParts.all (fun n => (p.contentType n).isSome)
  && p.rels.all (fun (s, rs) =>
       (match s with | .package => true | .part n => p.hasB n)
       && rs.all (fun r => p.hasB (r.resolve s.dir))
       && noDups (rs.map (·.id)))
  && p.mainDocument.length == 1

/-- The orphan check: every part is found within `parts.length` rounds. -/
def orphanCheck (p : Package) : Bool :=
  let f := p.found p.parts.length
  p.parts.all (fun n => f.any (·.key == n.key))

theorem mem_targetsFrom {p : Package} {srcs : List Source} {b : PartName}
    (h : b ∈ p.targetsFrom srcs) : ∃ a ∈ srcs, p.Edge a b := by
  simp only [targetsFrom, List.mem_flatMap] at h
  obtain ⟨⟨s, rs⟩, hmem, hb⟩ := h
  split at hb
  · rename_i hs
    simp only [List.mem_map] at hb
    obtain ⟨r, hr, rfl⟩ := hb
    exact ⟨s, by simpa using hs, rs, hmem, r, hr, rfl⟩
  · simp at hb

theorem found_reachable {p : Package} : ∀ k, ∀ b ∈ p.found k, p.Reachable b
  | 0, b, h => by
    obtain ⟨a, ha, he⟩ := mem_targetsFrom h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    exact .root he
  | k + 1, b, h => by
    simp only [found, List.mem_append] at h
    rcases h with h | h
    · exact found_reachable k b h
    · obtain ⟨a, ha, he⟩ := mem_targetsFrom h
      simp only [List.mem_map] at ha
      obtain ⟨n, hn, rfl⟩ := ha
      exact .step (found_reachable k n hn) he

/-- **The checker is sound**: a package it accepts follows every rule. -/
theorem check_sound {p : Package} (h : p.check = true) : p.WellFormed := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hnd, hty⟩, hrels⟩, hmain⟩ := h
  refine ⟨noDups_sound hnd, hty, ?_, ?_, ?_, hmain⟩
  · intro s rs hmem n hs
    have := (hrels (s, rs) hmem).1.1
    subst hs
    exact hasB_sound (by simpa using this)
  · intro s rs hmem r hr
    exact hasB_sound ((hrels (s, rs) hmem).1.2 r hr)
  · intro s rs hmem
    exact noDups_sound (hrels (s, rs) hmem).2

theorem orphanCheck_sound {p : Package} (h : p.orphanCheck = true) : p.NoOrphans := by
  simp only [orphanCheck, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  intro n hn
  obtain ⟨m, hm, hk⟩ := h n hn
  exact ⟨m, found_reachable _ m hm, hk⟩

/-! ## What a well-formed package guarantees a reader -/

/-- The main document exists, and it is the only one. -/
theorem WellFormed.main_exists {p : Package} (h : p.WellFormed) :
    ∃ m, p.mainDocument = [m] ∧ p.has m := by
  have hl := h.one_main
  match hm : p.mainDocument, hl with
  | [m], _ =>
    refine ⟨m, rfl, ?_⟩
    have : m ∈ p.mainDocument := by rw [hm]; exact List.mem_singleton_self m
    simp only [mainDocument, List.mem_filterMap] at this
    obtain ⟨r, hr, hm'⟩ := this
    split at hm'
    · cases hm'
      simp only [relsOf] at hr
      cases hlk : p.rels.lookup .package with
      | none => simp [hlk] at hr
      | some rs =>
        rw [hlk, Option.getD_some] at hr
        exact h.targets_exist .package rs (mem_of_lookup hlk) r hr
    · cases hm'

/-- Following any relationship never leaves the package. -/
theorem WellFormed.edge_lands {p : Package} (h : p.WellFormed) {a b} (e : p.Edge a b) :
    p.has b := by
  obtain ⟨rs, hmem, r, hr, rfl⟩ := e
  exact h.targets_exist a rs hmem r hr

/-- Every entry of the archive has a content type, so `[Content_Types].xml` is complete. -/
theorem WellFormed.contentType_total {p : Package} (h : p.WellFormed) {n} (hn : n ∈ p.allParts) :
    ∃ t, p.contentType n = some t :=
  Option.isSome_iff_exists.1 (h.typed n hn)

end Package
end Xlsx
