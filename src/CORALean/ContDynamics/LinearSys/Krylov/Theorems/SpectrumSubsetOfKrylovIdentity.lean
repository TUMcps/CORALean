import CORALean.Global.Tensor
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The spectrum of the Krylov matrix lies in the field of values of `σA`

[1, Eq. 3.4]: `spec(σT_m) ⊆ W(σT_m) ⊆ W(σA) ⊆ ℂ⁻`, the last in the nonexpansive case. With
the Krylov identity (2.2), `V_m*V_m = I` and `V_m*v_{m+1} = 0`, `T_m = V_m*AV_m`, so
`x*σT_mx = (V_mx)*σA(V_mx)` with `‖V_mx‖ = ‖x‖`; an eigenvector `x` of `σT_m` gives its
eigenvalue as `x*σT_mx/x*x`. The field of values is written as the set of Rayleigh quotients
`x*Mx/x*x`, `x ≠ 0`, the same set as `{x*Mx : ‖x‖₂ = 1}`.

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

open Matrix

open scoped ComplexOrder

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3.4]: under (2.2) with `V_m*V_m = I` and `V_m*v_{m+1} = 0`,
`spec(σT_m) ⊆ W(σT_m) ⊆ W(σA)`, and `W(σA) ⊆ ℂ⁻` (the nonexpansive case) gives
`spec(σT_m) ⊆ ℂ⁻`; here `V_m` has `m + 1` columns. -/
theorem Krylov.spectrum_subset_of_krylovIdentity (A : Mat ℂ n n) (V : Mat ℂ n (m + 1))
    (T : Mat ℂ (m + 1) (m + 1)) (τ σ : ℂ) (w : Fin n → ℂ)
    (hK : A * V = V * T + τ • vecMulVec w (Pi.single (Fin.last m) 1)) (hV : Vᴴ * V = 1)
    (hw : Vᴴ *ᵥ w = 0) :
    let W : ∀ {k : ℕ}, Mat ℂ k k → Set ℂ := fun M =>
      {z | ∃ x, x ≠ 0 ∧ z = (star x ⬝ᵥ (M *ᵥ x)) / (star x ⬝ᵥ x)}
    spectrum ℂ (σ • T) ⊆ W (σ • T) ∧ W (σ • T) ⊆ W (σ • A) ∧
      (W (σ • A) ⊆ {z | z.re ≤ 0} → spectrum ℂ (σ • T) ⊆ {z | z.re ≤ 0}) := by -- --- PROOF ---
  intro W
  -- the Galerkin form `T_m = V_m*AV_m`
  have hT : Vᴴ * A * V = T := by
    rw [Matrix.mul_assoc, hK, Matrix.mul_add, ← Matrix.mul_assoc, hV, Matrix.one_mul,
      Matrix.mul_smul, mul_vecMulVec, hw, zero_vecMulVec, smul_zero, add_zero]
  -- `x*Mx` read through `V_m`
  have hquad : ∀ (M : Mat ℂ n n) (x : Fin (m + 1) → ℂ),
      star x ⬝ᵥ ((Vᴴ * M * V) *ᵥ x) = star (V *ᵥ x) ⬝ᵥ (M *ᵥ (V *ᵥ x)) := by
    intro M x
    rw [star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
  have hnorm : ∀ x : Fin (m + 1) → ℂ, star (V *ᵥ x) ⬝ᵥ (V *ᵥ x) = star x ⬝ᵥ x := by
    intro x
    have h := hquad 1 x
    rw [Matrix.mul_one, hV, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h.symm
  have h1 : spectrum ℂ (σ • T) ⊆ W (σ • T) := by
    intro μ hμ
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff] at hμ
    obtain ⟨x, hx0, hx⟩ := hμ
    -- `σT_m x = μ x`
    have hev : (σ • T) *ᵥ x = μ • x := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, sub_eq_zero] at hx
      exact hx.symm
    refine ⟨x, hx0, ?_⟩
    rw [hev, dotProduct_smul, smul_eq_mul, mul_div_assoc, div_self, mul_one]
    exact (dotProduct_star_self_eq_zero.not).2 hx0
  have h2 : W (σ • T) ⊆ W (σ • A) := by
    rintro z ⟨x, hx0, rfl⟩
    have hVx : V *ᵥ x ≠ 0 := by
      intro h
      apply hx0
      rw [← dotProduct_star_self_eq_zero, ← hnorm, h, dotProduct_zero]
    refine ⟨V *ᵥ x, hVx, ?_⟩
    rw [hnorm, ← hT, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
      hquad]
  exact ⟨h1, h2, fun h3 => h1.trans (h2.trans h3)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
