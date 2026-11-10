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


-- ==============================  `SetIntersection.convex_toSet`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An intersection of convex members is convex, `univ` at the empty list included. -/
theorem SetIntersection.convex_toSet [ContSetLike S α] [ConvexSet S α] (I : SetIntersection S) :
    Convex ℝ (ContSetLike.toSet I) :=
  convex_iInter₂ fun s _ => ConvexSet.convex_toSet s

end

section
variable {S α : Type}


-- ===============================  `SetIntersection.mem_toSet`  ================================ --
-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Unfolds membership to a fact about every branch, for every proof below. -/
theorem SetIntersection.mem_toSet [ContSetLike S α] {I : SetIntersection S} {x : α} :
    x ∈ ContSetLike.toSet I ↔ ∀ s ∈ I.sets, x ∈ ContSetLike.toSet s := by
  show x ∈ SetIntersection.toSet I ↔ _
  simp [SetIntersection.toSet]


-- ===============================  `SetIntersection.toSet_ofFn`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A `Fin k`-indexed family, listed in order, denotes the intersection over its index. -/
theorem SetIntersection.toSet_ofFn [ContSetLike S α] {k : ℕ} (f : Fin k → S) :
    ContSetLike.toSet (⟨List.ofFn f⟩ : SetIntersection S) = ⋂ i, ContSetLike.toSet (f i) := by
  ext x
  simp [SetIntersection.mem_toSet, List.mem_ofFn]


-- =============================  `SetIntersection.mem_toSet_ofFn`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Membership in a `Fin`-indexed family's intersection, member by index. -/
theorem SetIntersection.mem_toSet_ofFn [ContSetLike S α] {k : ℕ} {f : Fin k → S} {x : α} :
    x ∈ ContSetLike.toSet (⟨List.ofFn f⟩ : SetIntersection S) ↔
      ∀ i, x ∈ ContSetLike.toSet (f i) := by
  rw [SetIntersection.toSet_ofFn, Set.mem_iInter]


-- ==============================  `SetIntersection.toSet_subset`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The intersection lies in each of its members: one member is already an outer bound. -/
theorem SetIntersection.toSet_subset [ContSetLike S α] {I : SetIntersection S} {s : S}
    (hs : s ∈ I.sets) : ContSetLike.toSet I ⊆ ContSetLike.toSet s :=
  fun _ hx => SetIntersection.mem_toSet.mp hx s hs


-- ============================  `SetIntersection.subset_toSet_iff`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A set lies in the intersection iff it lies in every member: containment, member by member. -/
theorem SetIntersection.subset_toSet_iff [ContSetLike S α] {I : SetIntersection S} {X : Set α} :
    X ⊆ ContSetLike.toSet I ↔ ∀ s ∈ I.sets, X ⊆ ContSetLike.toSet s :=
  ⟨fun h _ hs => h.trans (SetIntersection.toSet_subset hs),
    fun h _ hx => SetIntersection.mem_toSet.mpr fun s hs => h s hs hx⟩


-- ===========================  `SetIntersection.toSet_subset_ofFn`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A `Fin k`-indexed family's intersection lies in its member `i`. -/
theorem SetIntersection.toSet_subset_ofFn [ContSetLike S α] {k : ℕ} (f : Fin k → S) (i : Fin k) :
    ContSetLike.toSet (⟨List.ofFn f⟩ : SetIntersection S) ⊆ ContSetLike.toSet (f i) :=
  SetIntersection.toSet_subset (List.mem_ofFn.mpr ⟨i, rfl⟩)

end


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
