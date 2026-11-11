module

public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Definitions.Fiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A polynomial zonotope is the union of its fibers

A point of `pZ` is a point of its fiber at some factor values in the unit box, and conversely.

## Inputs
* `pZ` – polynomial zonotope
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` is in the set iff it is in the fiber at some `a` in the unit box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set is the union of the fibers at factor values in the unit box. -/
theorem PolyZonotope.mem_toSet_iff_fiber (pZ : PolyZonotope (Vec 𝕋 n))
    (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ pZ.toSet ↔ ∃ a : Fin pZ.p → ℝ, (∀ k, |a k| ≤ 1) ∧ x ∈ pZ.fiber a := by -- --- PROOF ---
  constructor
  · rintro ⟨y, hy, e, he, rfl⟩
    obtain ⟨a, β, ha, hβ, hy⟩ := PolyZonotope.mem_nominalSet_iff.mp hy
    refine ⟨a, ha, (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β, hβ, e, he, ?_⟩⟩
    funext i
    repeat rw [PolyZonotope.nominal_point_eq]
    simp only [Pi.add_apply, hy i]
  · rintro ⟨a, ha, hx⟩
    obtain ⟨β, hβ, e, he, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
    refine ⟨pZ.nominal.point a + fun i => ∑ j, toReal (pZ.GI j i) * β j,
      PolyZonotope.mem_nominalSet_iff.mpr ⟨a, β, ha, hβ, fun i => ?_⟩, e, he, ?_⟩
    · repeat rw [PolyZonotope.nominal_point_eq]
      simp only [Pi.add_apply]
    · rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
