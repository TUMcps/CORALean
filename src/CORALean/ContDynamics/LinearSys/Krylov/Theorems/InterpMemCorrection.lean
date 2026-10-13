import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ExpDiffMemCorrectionSet

/-!
# The Krylov approximation between two time points

[1, Lemma III.3], (16): with `x̂_h(t) = ‖x₀‖ V e^{Ht} e₁` and the first Arnoldi vector
`‖x₀‖ V e₁ = x₀`, for every `t ∈ [0, δ]`,
`x̂_h(t) ∈ x₀ + (t/δ)(x̂_h(δ) - x₀) ⊕ ‖x₀‖ V F e₁`. The difference is `‖x₀‖ V D e₁` with
`D = e^{Ht} - I - (t/δ)(e^{Hδ} - I)`, which lies in `F` by `expDiff_mem_correctionSet`. Any
scalar `β` stands for `‖x₀‖`, and the first-column property is the hypothesis.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.interp_mem_correction (V : Mat ℝ n m) (H : Mat ℝ m m) (e₁ : Vec ℝ m)
    (β : ℝ) (x₀ : Vec ℝ n) (hV : β • (V *ᵥ e₁) = x₀) {δ : ℝ} (hδ : 0 < δ) {η : ℕ} (hη : 1 ≤ η)
    {t : ℝ} (ht0 : 0 ≤ t) (htδ : t ≤ δ) :
    ∃ F ∈ Krylov.correctionSet H δ η,
      β • (V *ᵥ (exp (t • H) *ᵥ e₁))
        = x₀ + (t / δ) • (β • (V *ᵥ (exp (δ • H) *ᵥ e₁)) - x₀)
          + β • (V *ᵥ (F *ᵥ e₁)) := by -- --- PROOF ---
  refine ⟨_, Krylov.expDiff_mem_correctionSet H hδ hη ht0 htδ, ?_⟩
  -- `‖x₀‖ V (·) e₁` is linear in the matrix, and `I` goes to `x₀`
  rw [← hV]
  simp only [sub_mulVec, smul_mulVec, one_mulVec, mulVec_sub, mulVec_smul, smul_sub,
    smul_comm β (t / δ)]
  abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
