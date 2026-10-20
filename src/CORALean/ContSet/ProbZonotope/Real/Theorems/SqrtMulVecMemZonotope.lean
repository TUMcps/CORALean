module

public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# A mean plus the covariance's square root applied to a cube lands in the confidence set

For a mean `μ` of `P`, the point `μ + g β` is in `zonotope(probZ, m)` whenever the coefficients
`β` lie in the cube `[-m, m]ⁿ`, `g` the symmetric square root of the covariance: it is
`μ + Σⱼ (βⱼ/m) (m g·ⱼ)`. This is the step of `zonotope_prob` that turns the probability of the
cube into the probability of the confidence set, and of `ellipsoid_subset_zonotope`, which turns
the `m`-sigma ellipsoid into it.

## Inputs
* `P` – probabilistic zonotope
* `μ` – mean of length `n`
* `m` – real number
* `β` – vector of length `n`

## Hypotheses
* `hμ` – `μ` lies in `P.Z`
* `hm` – `0 < m`
* `hβ` – `∀ j, |β j| ≤ m`

## Conclusion
* `μ` plus `√Σ β` lies in the confidence zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.add_sqrt_mulVec_mem_zonotope (P : ProbZonotope n) {μ : Vec ℝ n}
    (hμ : μ ∈ P.Z.construct) {m : ℝ} (hm : 0 < m) {β : Vec ℝ n}
    (hβ : ∀ j, |β j| ≤ m) : -- --- CONCL ---
    μ + CFC.sqrt P.cov *ᵥ β ∈ (P.zonotope m).construct := by -- --- PROOF ---
  rw [ProbZonotope.zonotope, ← Zonotope.plus_exact]
  refine Set.add_mem_add hμ ⟨fun j => β j / m, fun j => ?_, ?_⟩
  · rw [abs_div, abs_of_pos hm, div_le_one hm]
    exact hβ j
  · funext i
    simp only [confidenceZonotope, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change CFC.sqrt P.cov i j * β j = β j / m * (m * CFC.sqrt P.cov i j)
    field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
