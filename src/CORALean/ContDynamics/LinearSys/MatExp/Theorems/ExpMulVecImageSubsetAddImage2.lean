module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpDiffMatrices
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiffMulVecMemCorrectionMatrix

@[expose] public section

/-!
# The image of a set under `e^{At}` lies in the set plus `ΔR`

`[1, Eq. 6]`: `e^{At} Z ⊆ Z + M Z` for every `t ∈ [0, r]`, `Z` standing for `η(R(0), γ)`,
with `M Z` the `ΔR` of [2, Thm. 3]'s correction matrix.

## Inputs
* `A` – system matrix
* `r` – step length
* `m` – Taylor order offset
* `t` – time
* `Z` – vector set

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the exponential image of the set lies in the set plus the variation matrices applied to it

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". In Proc. of the European Control Conference
      (ECC), pp. 625-630, 2009.
* [2] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". In Proc. of the 46th IEEE Conference on Decision and Control (CDC),
      2007, pp. 726-732.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{At} Z ⊆ Z + ΔR` for `t ∈ [0, r]`. -/
theorem MatExp.expMulVec_image_subset_add_image2 (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (Z : Set (Vec ℝ n)) : -- --- CONCL ---
    (fun x => exp (t • A) *ᵥ x) '' Z
      ⊆ Z + Set.image2 (fun B x => B *ᵥ x) (MatExp.expDiffMatrices A r m) Z := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨F, hF, h⟩ := MatExp.expDiff_mulVec_mem_correctionMatrix A hr hε ht0 htr x
  refine ⟨x, hx, ((t / r) • (exp (r • A) - 1) + F) *ᵥ x,
    ⟨_, ⟨t / r, ⟨div_nonneg ht0 hr.le, (div_le_one hr).2 htr⟩, F, hF, rfl⟩, x, hx, rfl⟩, ?_⟩
  simp only [add_mulVec, smul_mulVec]
  have h' : exp (t • A) *ᵥ x = x + ((t / r) • (exp (r • A) - 1) *ᵥ x + F *ᵥ x) := by
    rw [← h]; abel
  rw [h']


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
