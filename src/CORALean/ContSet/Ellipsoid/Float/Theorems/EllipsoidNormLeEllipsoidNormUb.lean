module

public import CORALean.ContSet.Ellipsoid.Float.Operations.EllipsoidNormUb
public import CORALean.ContSet.Ellipsoid.Real.Theorems.EllipsoidNormLeOneIff
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsUnitShape

@[expose] public section

/-!
# `Ellipsoid.ellipsoidNormUb` bounds the ellipsoid norm

The checked equation, read as reals, is `Q w = p`. At full rank the nominal `Q` is the stored one,
positive semi-definite and invertible (`isUnit_shape`), so `Q⁻¹ p = w` and the norm is
`√(pᵀ w)`, `pᵀ w = wᵀ Q w ≥ 0`, which the rounded-up dot product and square root bound. A refused
`Q` has rank `0`, so full rank is dimension `0`, where the norm is `0`.

## Inputs
* `prec` – Newton steps of the root
* `E` – ellipsoid
* `p` – point
* `w` – solve of `Q w = p`

## Hypotheses
* `hr` – nominal shape has full rank

## Conclusion
* every returned bound is at least the ellipsoid norm of `p`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open FloatOps SoundFloatArithmetic ToRat InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.ellipsoidNorm_le_ellipsoidNormUb {prec : ℕ} {E : Ellipsoid 𝕋 n} {p w : Vec 𝕋 n}
    (hr : (nominal E).ellipsoid.rank = n) : -- --- CONCL ---
    ∀ t ∈ E.ellipsoidNormUb prec p w,
      (nominal E).ellipsoid.ellipsoidNorm (toRealVec p) ≤ toReal t := by -- --- PROOF ---
  intro t (h : E.ellipsoidNormUb prec p w = some t)
  simp only [Ellipsoid.ellipsoidNormUb] at h
  split_ifs at h with hsol
  simp only [Option.some.injEq] at h
  rw [Bool.and_eq_true] at hsol
  obtain ⟨hsol, -⟩ := hsol
  subst h
  simp only [List.all_eq_true, List.mem_finRange, forall_const, decide_eq_true_eq] at hsol
  -- the equation read as reals: `Q w = p`
  have hp : toRealVec p = toRealMat E.Q *ᵥ toRealVec w := funext fun i => by
    have := congrArg (fun q : ℚ => (q : ℝ)) (hsol i)
    simp only [Rat.cast_sum, Rat.cast_mul, toReal_toRat] at this
    simp [Matrix.mulVec, dotProduct, toRealMat, toRealVec, this]
  by_cases hpsd : (toRealMat E.Q).PosSemidef
  · -- full rank: `Q⁻¹ p = w`, and the norm is `√(pᵀ w)`
    rw [Ellipsoid.nominal_of_psd hpsd] at hr ⊢
    have hU := Real.Ellipsoid.isUnit_shape _ hr
    have hinv : (toRealMat E.Q)⁻¹ *ᵥ toRealVec p = toRealVec w := by
      rw [hp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
    have hnn : 0 ≤ toRealVec p ⬝ᵥ toRealVec w := by
      rw [hp, dotProduct_comm]
      simpa using hpsd.dotProduct_mulVec_nonneg (toRealVec w)
    show Real.sqrt |toRealVec p ⬝ᵥ ((toRealMat E.Q)⁻¹ *ᵥ toRealVec p)| ≤ _
    rw [hinv, abs_of_nonneg hnn]
    exact le_trans (Real.sqrt_le_sqrt (le_dotUp p w)) (le_sqrtUp prec _)
  · -- refused: rank `0`, so dimension `0`, where the norm is `0`
    have hn : n = 0 := by
      rw [← hr]
      show (nominal E).ellipsoid.Q.rank = 0
      rw [Ellipsoid.nominal_Q_eq, if_neg hpsd, Matrix.rank_zero]
    have hdot : ∀ x y : Vec ℝ n, x ⬝ᵥ y = 0 := fun x y => by
      subst hn
      simp [dotProduct]
    show Real.sqrt |_| ≤ _
    rw [hdot, abs_zero, Real.sqrt_zero]
    exact sqrtUp_nonneg prec _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
