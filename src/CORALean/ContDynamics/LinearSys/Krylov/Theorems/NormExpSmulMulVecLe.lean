module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# A matrix with field of values in the closed left half-plane generates contractions

[1, Eq. 3.1b] uses `‖E(t - s)‖₂ ≤ 1`, which `W(σA) ⊆ ℂ⁻` (the nonexpansive case) gives for
`E(t) = e^{σtA}`, `t ≥ 0`. Here for any complex `M` with `Re(x*Mx) ≤ 0` for all `x`: the squared
Euclidean norm of `e^{sM}x` has derivative `2Re(y*My) ≤ 0` at `y = e^{sM}x`, so it does not
increase. `‖·‖₂` is the norm of `EuclideanSpace ℂ (Fin n)`, reached by `WithLp.toLp 2`.

## References

* [1] T. Jawecki, W. Auzinger, O. Koch. "Computable upper error bounds for Krylov approximations
  to matrix exponentials and associated φ-functions". BIT Numerical Mathematics, 60(1):157-197,
  2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3.1b]'s step: `Re(x*Mx) ≤ 0` for all `x` (`W(M) ⊆ ℂ⁻`) gives `‖e^{sM}x‖₂ ≤ ‖x‖₂` for
`s ≥ 0`. -/
theorem Krylov.norm_exp_smul_mulVec_le (M : Mat ℂ n n)
    (hM : ∀ x : Fin n → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re ≤ 0) (x : Fin n → ℂ) {s : ℝ}
    (hs : 0 ≤ s) : -- --- STMT ---
    ‖(WithLp.toLp 2 (exp (s • M) *ᵥ x) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := by -- --- PROOF ---
  -- `B ↦ Bx`, into Euclidean space, as a continuous ℝ-linear map
  let L : Mat ℂ n n →ₗ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun B => WithLp.toLp 2 (B *ᵥ x)
      map_add' := fun B C => by rw [Matrix.add_mulVec, WithLp.toLp_add]
      map_smul' := fun r B => by
        rw [Matrix.smul_mulVec, RingHom.id_apply, WithLp.toLp_smul] }
  set Y : ℝ → EuclideanSpace ℂ (Fin n) := fun r => WithLp.toLp 2 (exp (r • M) *ᵥ x) with hYdef
  have hY : ∀ r, HasDerivAt Y (WithLp.toLp 2 (M *ᵥ (exp (r • M) *ᵥ x))) r := by
    intro r
    have h := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M r)
    have h2 : HasDerivAt Y ((LinearMap.toContinuousLinearMap L) (M * exp (r • M))) r := h
    refine h2.congr_deriv ?_
    simp [L, Matrix.mulVec_mulVec]
  -- `d/dr ‖Y r‖² = 2 Re ⟪Y r, M Y r⟫ ≤ 0`
  have hg : ∀ r, HasDerivAt (fun r => ‖Y r‖ ^ 2)
      (2 * (star (exp (r • M) *ᵥ x) ⬝ᵥ (M *ᵥ (exp (r • M) *ᵥ x))).re) r := by
    intro r
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r ((hY r).inner ℂ (hY r))
    have heq : (fun r => ‖Y r‖ ^ 2) = Complex.reCLM ∘ fun r => inner ℂ (Y r) (Y r) := by
      funext r
      simp only [Function.comp_apply, Complex.reCLM_apply]
      exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Y r)
    rw [heq]
    -- `Re(⟪Y, MY⟫ + ⟪MY, Y⟫) = 2Re(Y*MY)`
    refine h.congr_deriv ?_
    simp only [Complex.reCLM_apply, Complex.add_re, hYdef, EuclideanSpace.inner_toLp_toLp]
    rw [← Complex.conj_re (star _ ⬝ᵥ _), dotProduct_comm (exp (r • M) *ᵥ x), two_mul]
    congr 1
    rw [Complex.conj_re, dotProduct_comm]
    show _ = (star (star (exp (r • M) *ᵥ x) ⬝ᵥ M *ᵥ exp (r • M) *ᵥ x)).re
    rw [← star_dotProduct_star, star_star]
  -- so `‖Y‖²` does not increase from `Y 0 = x`
  have hanti : Antitone fun r => ‖Y r‖ ^ 2 :=
    antitone_of_deriv_nonpos (fun r => (hg r).differentiableAt) fun r => by
      rw [(hg r).deriv]
      nlinarith [hM (exp (r • M) *ᵥ x)]
  have h := hanti hs
  simp only [hYdef, zero_smul, exp_zero, one_mulVec] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
