module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Operations.AndPoint
public import CORALean.ContSet.OptEmpty.Theorems.Basic

@[expose] public section

/-!
# `and_` of an ellipsoid and a point is exact

`E ∩ {p}` is the point `p` as a degenerate ellipsoid when `p ∈ E` and `∅` otherwise: the
denotation of `Ellipsoid.andPoint` equals the intersection, an equality and not an enclosure.

## Inputs
* `E` – ellipsoid
* `p` – point

## Hypotheses
* none

## Conclusion
* the result is exactly `E ∩ {p}`
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The ellipsoid of zero shape denotes the single point. -/
theorem Ellipsoid.aux_construct_ofPoint (p : Vec ℝ n) : -- --- CONCL ---
    (Ellipsoid.ofPoint p).construct = {p} := by -- --- PROOF ---
  have hG : (Ellipsoid.ofPoint p).G = 0 := (Ellipsoid.G_eq_zero_iff _).2 rfl
  ext x
  constructor
  · rw [Ellipsoid.construct_eq_sqrt]
    rintro ⟨u, -, rfl⟩
    rw [hG, Matrix.zero_mulVec, add_zero]
    rfl
  · rintro rfl
    exact Ellipsoid.mem_ofPoint x


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.andPoint_exact (E : Ellipsoid n) (p : Vec ℝ n) : -- --- CONCL ---
    ContSet.construct (E.andPoint p) = E.construct ∩ {p} := by -- --- PROOF ---
  unfold Ellipsoid.andPoint
  split_ifs with h
  · rw [OptEmpty.construct_of]
    change (Ellipsoid.ofPoint p).construct = _
    rw [Ellipsoid.aux_construct_ofPoint]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
    constructor
    · rintro rfl; exact ⟨h, rfl⟩
    · exact fun hx => hx.2
  · rw [OptEmpty.construct_empty]
    ext x
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_singleton_iff, false_iff,
      not_and]
    rintro hx rfl
    exact h hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
