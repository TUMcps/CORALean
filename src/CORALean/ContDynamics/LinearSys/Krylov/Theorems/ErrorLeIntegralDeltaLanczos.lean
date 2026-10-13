module

public import Mathlib.Analysis.Matrix.Hermitian
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorLeExpMinIntegralDelta

@[expose] public section

/-!
# The Lanczos error for `e^{iτH}v` is bounded by `β_{k+1}∫₀^τ|h(t)|dt`

[1, Eq. 6.4]: for Hermitian `H` the Lanczos relation (6.2), `HV_k = V_kT_k + β_{k+1}v_{k+1}e_k*`,
is (3.1) for the skew-Hermitian `A = -iH` with `H_k = -iT_k` and `h_{k+1,k} = β_{k+1}` (up to the
unit factor `-i`), `ν(A) = 0`, so Thm. 3.1 (`Krylov.error_le_exp_min_integral_delta`) gives
`‖e^{iτH}v - V_ke^{iτT_k}e₁‖₂ ≤ β_{k+1}∫₀^τ|h(t)|dt`, `h(t) = e_k*e^{itT_k}e₁`. This is the first
inequality of (6.4); the second, `β_{k+1} ≤ ‖H‖`, is not formalized. Stated for Hermitian `H`, any
complex `T_k`, `β_{k+1}` and `v_{k+1}` with (6.2); the tridiagonal form of `T_k` is not used.

## References

* [1] H. Wang, Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix
  exponentials". SIAM Journal on Matrix Analysis and Applications, 38(1):155-187, 2017.
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

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 6.4]: under (6.2), Hermitian `H` and `v = V_ke₁`, `‖e^{itH}v - V_ke^{itT_k}e₁‖₂ ≤
|β_{k+1}|‖v_{k+1}‖₂ ∫₀ᵗ|h(s)|ds` for `t ≥ 0`; `V_k` has `m + 1` columns. -/
theorem Krylov.error_le_integral_delta_lanczos (H : Mat ℂ n n) (hH : H.IsHermitian)
    (V : Mat ℂ n (m + 1)) (T : Mat ℂ (m + 1) (m + 1)) (β : ℂ) (w : Fin n → ℂ)
    (hK : H * V = V * T + β • vecMulVec w (Pi.single (Fin.last m) 1)) {t : ℝ} (ht : 0 ≤ t) :
    let v := V *ᵥ Pi.single 0 1
    let h : ℝ → ℂ := fun s => exp (s • (Complex.I • T)) (Fin.last m) 0
    ‖(WithLp.toLp 2 (exp (t • (Complex.I • H)) *ᵥ v -
          V *ᵥ (exp (t • (Complex.I • T)) *ᵥ Pi.single 0 1)) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖β‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n))‖ *
        ∫ s in (0 : ℝ)..t, ‖h s‖ := by -- --- PROOF ---
  intro v h
  -- (3.1) for `A = -iH`, `H_k = -iT_k`, `h_{k+1,k} = -iβ_{k+1}`
  have hK' : ((-Complex.I) • H) * V = V * ((-Complex.I) • T) +
      (-Complex.I * β) • vecMulVec w (Pi.single (Fin.last m) 1) := by
    rw [Matrix.smul_mul, hK, smul_add, Matrix.mul_smul, smul_smul]
  -- `A = -iH` is skew-Hermitian, so `Re(x*Ax) = 0`
  have hA : ∀ x : Fin n → ℂ, (0 : ℝ) * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ (((-Complex.I) • H) *ᵥ x)).re := by
    intro x
    have h0 := Matrix.IsHermitian.im_star_dotProduct_mulVec_self hH x
    have h0' : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by simpa using h0
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, h0']
    simp
  have hmain := Krylov.error_le_exp_min_integral_delta ((-Complex.I) • H) V ((-Complex.I) • T)
    (-Complex.I * β) w hK' 0 hA ht
  simp only [neg_smul, neg_neg, min_self, neg_zero, zero_mul, Real.exp_zero, one_mul,
    norm_mul, norm_neg, Complex.norm_I] at hmain
  exact hmain

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
