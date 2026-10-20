module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemWalkEdgesIff
public import Mathlib.Tactic.Module
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The zonogon and its walk edges are symmetric about the center

`x ↦ 2c - x` negates every coefficient, so it maps the zonotope to itself, and it maps the sign
corner `s` to the corner `¬ s`, so it swaps the two blocks of the walk and maps the walk edges to
themselves. [1, Alg. 3] and [1, Alg. 4] use it to get the upper end of a section from the lower.

## Inputs
* `Z` – zonotope
* `x` – point on the walk edges

## Hypotheses
* `hx` – `x` lies on the walk edges

## Conclusion
* the reflection of `x` through the center lies on the walk edges

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The point reflection of a sign corner is the opposite sign corner. -/
theorem Zonotope.aux_corner_symm (Z : Zonotope α) (s : Fin Z.h → Bool) : -- --- CONCL ---
    (2 : ℝ) • Z.c - Z.corner s = Z.corner (fun j => !s j) := by -- --- PROOF ---
  simp only [Zonotope.corner]
  have : ∀ j, (if (!s j) = true then (1 : ℝ) else -1) • Z.G j
      = -((if s j = true then (1 : ℝ) else -1) • Z.G j) := fun j => by
    cases s j <;> simp
  simp only [this, Finset.sum_neg_distrib]
  module

/-- The point reflection maps a segment onto the segment of the reflected ends. -/
theorem Zonotope.aux_segment_symm (c A B x : α) (hx : x ∈ segment ℝ A B) :
    (2 : ℝ) • c - x ∈ segment ℝ ((2 : ℝ) • c - A) ((2 : ℝ) • c - B) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  refine ⟨a, b, ha, hb, hab, ?_⟩
  obtain rfl : b = 1 - a := by linarith
  module


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.walkEdges_central_symm (Z : Zonotope α) {x : α}
    (hx : x ∈ Z.walkEdges) : -- --- CONCL ---
    (2 : ℝ) • Z.c - x ∈ Z.walkEdges := by -- --- PROOF ---
  obtain ⟨k, hk | hk⟩ := (Z.mem_walkEdges_iff x).mp hx
  · refine (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inr ?_⟩
    have := Zonotope.aux_segment_symm Z.c _ _ _ hk
    rw [Zonotope.aux_corner_symm, Zonotope.aux_corner_symm] at this
    simpa only [Bool.not_not] using this
  · refine (Z.mem_walkEdges_iff _).mpr ⟨k, Or.inl ?_⟩
    have := Zonotope.aux_segment_symm Z.c _ _ _ hk
    rw [Zonotope.aux_corner_symm, Zonotope.aux_corner_symm] at this
    simpa only [Bool.not_not] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
