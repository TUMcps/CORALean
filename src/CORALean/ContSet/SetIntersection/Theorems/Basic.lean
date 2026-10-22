module

public import CORALean.ContSet.SetIntersection.SetIntersection
public import CORALean.ContSet.ContSet.Definitions.Interfaces

@[expose] public section

/-!
# `ContSet/SetIntersection/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

section
variable {S α : Type} [AddCommGroup α] [Module ℝ α]


-- ============================  `SetIntersection.convex_construct`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An intersection of convex members is convex, `univ` at the empty list included. -/
theorem SetIntersection.convex_construct [ContSet S α] [ConvexSet S α] (I : SetIntersection S) :
    Convex ℝ (ContSet.construct I) :=
  convex_iInter₂ fun s _ => ConvexSet.convex_construct s

end

section
variable {S α : Type}


-- =============================  `SetIntersection.mem_construct`  ============================== --
-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Unfolds membership to a fact about every branch, for every proof below. -/
theorem SetIntersection.mem_construct [ContSet S α] {I : SetIntersection S} {x : α} :
    x ∈ ContSet.construct I ↔ ∀ s ∈ I.sets, x ∈ ContSet.construct s := by
  show x ∈ SetIntersection.construct I ↔ _
  simp [SetIntersection.construct]


-- =============================  `SetIntersection.construct_ofFn`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A `Fin k`-indexed family, listed in order, denotes the intersection over its index. -/
theorem SetIntersection.construct_ofFn [ContSet S α] {k : ℕ} (f : Fin k → S) :
    ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S) = ⋂ i, ContSet.construct (f i) := by
  ext x
  simp [SetIntersection.mem_construct, List.mem_ofFn]


-- ============================  `SetIntersection.construct_subset`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The intersection lies in each of its members: one member is already an outer bound. -/
theorem SetIntersection.construct_subset [ContSet S α] {I : SetIntersection S} {s : S}
    (hs : s ∈ I.sets) : ContSet.construct I ⊆ ContSet.construct s :=
  fun _ hx => SetIntersection.mem_construct.mp hx s hs


-- =========================  `SetIntersection.construct_subset_ofFn`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A `Fin k`-indexed family's intersection lies in its member `i`. -/
theorem SetIntersection.construct_subset_ofFn [ContSet S α] {k : ℕ} (f : Fin k → S) (i : Fin k) :
    ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S) ⊆ ContSet.construct (f i) :=
  SetIntersection.construct_subset (List.mem_ofFn.mpr ⟨i, rfl⟩)


-- ===========================  `SetIntersection.mem_construct_ofFn`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Membership in a `Fin`-indexed family's intersection, member by index. -/
theorem SetIntersection.mem_construct_ofFn [ContSet S α] {k : ℕ} {f : Fin k → S} {x : α} :
    x ∈ ContSet.construct (⟨List.ofFn f⟩ : SetIntersection S) ↔
      ∀ i, x ∈ ContSet.construct (f i) := by
  rw [SetIntersection.construct_ofFn, Set.mem_iInter]


-- ==========================  `SetIntersection.subset_construct_iff`  ========================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A set lies in the intersection iff it lies in every member: containment, member by member. -/
theorem SetIntersection.subset_construct_iff [ContSet S α] {I : SetIntersection S} {X : Set α} :
    X ⊆ ContSet.construct I ↔ ∀ s ∈ I.sets, X ⊆ ContSet.construct s :=
  ⟨fun h _ hs => h.trans (SetIntersection.construct_subset hs),
    fun h _ hx => SetIntersection.mem_construct.mpr fun s hs => h s hs hx⟩

end


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
