module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope

@[expose] public section

/-!
# An ellipsoid as a zonotope

## Inputs
* `E` – ellipsoid
* `m` – number of generators
* `S` – generators
* `l` – squared ball radius

## Hypotheses
* `hl` – squared radius positive
* `hball` – ball of that radius lies in the zonotope

## Conclusion
* ellipsoid is contained in the scaled zonotope

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 4]: a ball of radius `√l` inside `Z(S, 0)` — `l ≤ ⌊Z(S, 0)⌋²` — makes the scaled
zonotope enclose the ellipsoid. -/
theorem Ellipsoid.zonotopeNorm_contains (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ n)
    {l : ℝ} (hl : 0 < l)
    (hball : ∀ u : Vec ℝ n, ‖u‖₂ ≤ √l → u ∈ (⟨m, 0, S⟩ : Zonotope (Vec ℝ n)).construct) :
    E.construct ⊆ (E.zonotopeNorm S l).construct := by -- --- PROOF ---
  rw [E.construct_eq_sqrt]
  rintro _ ⟨u, hu, rfl⟩
  have hs : 0 < √l := Real.sqrt_pos.mpr hl
  -- `√l u` is a combination of the points, so `u` is one of the scaled points
  obtain ⟨β, hβ, heq⟩ := hball (√l • u) (by
    rw [norm₂_smul, abs_of_pos hs]
    exact mul_le_of_le_one_right hs.le hu)
  rw [zero_add] at heq
  change ∀ j : Fin m, |β j| ≤ 1 at hβ
  refine ⟨(β : Fin m → ℝ), hβ, ?_⟩
  show E.q + E.G *ᵥ u = E.q + ∑ j, β j • ((√l)⁻¹ • (E.G *ᵥ S j))
  have hu' : u = (√l)⁻¹ • ∑ j, β j • S j := by
    rw [← heq, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hu', Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum]
  simp only [Matrix.mulVec_smul, smul_comm (√l)⁻¹]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
