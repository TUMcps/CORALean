module

public import CORALean.ContSet.Ellipsoid.Float.Operations.PsdCheck
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QuadNonnegOfDominant
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# A passed `psdCheck` makes every symmetric matrix of the interval positive semi-definite

`R = X' - L Lᵀ` lies entrywise between the check's two roundings, so its off-diagonal magnitudes
are below the rounded-up maxima and its diagonal above the lower bounds: diagonally dominant, and
symmetric with `X'`, so positive semi-definite (`quad_nonneg_of_dominant`); and `X' = R + L Lᵀ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed check makes every symmetric matrix of `X` positive semi-definite. -/
theorem Ellipsoid.posSemidef_of_psdCheck {X : Interval (Mat 𝕋 n n)} {L : Mat 𝕋 n n}
    (h : Ellipsoid.psdCheck X L = true) {Xr : Mat ℝ n n}
    (hX : ∀ i j, toReal (X.inf i j) ≤ Xr i j ∧ Xr i j ≤ toReal (X.sup i j))
    (hsym : ∀ i j, Xr i j = Xr j i) : Xr.PosSemidef := by -- --- PROOF ---
  set Lr : Mat ℝ n n := toRealMat L with hLr
  set R : Mat ℝ n n := Xr - Lr * Lrᵀ with hR
  set lo : Mat 𝕋 n n := fun i j => subDown (X.inf i j) (dotUp (L i) (L j)) with hlo
  set hi : Mat 𝕋 n n := fun i j => subUp (X.sup i j) (dotDown (L i) (L j)) with hhi
  -- each residual entry between its two roundings
  have hLL : ∀ i j, (Lr * Lrᵀ) i j = ∑ k, toReal (L i k) * toReal (L j k) := fun i j => by
    simp [hLr, Matrix.mul_apply, toRealMat]
  have hbr : ∀ i j, toReal (lo i j) ≤ R i j ∧ R i j ≤ toReal (hi i j) := by
    intro i j
    have e1 := subDown_le_sub (X.inf i j) (dotUp (L i) (L j))
    have e2 := sub_le_subUp (X.sup i j) (dotDown (L i) (L j))
    have e3 := le_dotUp (L i) (L j)
    have e4 := dotDown_le (L i) (L j)
    have hRij : R i j = Xr i j - ∑ k, toReal (L i k) * toReal (L j k) := by
      rw [hR, Matrix.sub_apply, hLL]
    rw [hRij]
    exact ⟨by simp only [hlo]; linarith [(hX i j).1], by simp only [hhi]; linarith [(hX i j).2]⟩
  have habs : ∀ i j, |R i j| ≤ toReal (maximum (hi i j) (neg (lo i j))) := by
    intro i j
    rw [toReal_maximum, toReal_neg, abs_le]
    constructor
    · linarith [le_max_right (toReal (hi i j)) (-toReal (lo i j)), (hbr i j).1]
    · linarith [le_max_left (toReal (hi i j)) (-toReal (lo i j)), (hbr i j).2]
  -- symmetric, as `Xr` and `L Lᵀ` are
  have hsymR : ∀ i j, R i j = R j i := by
    intro i j
    rw [hR, Matrix.sub_apply, Matrix.sub_apply, hLL, hLL, hsym i j]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => mul_comm _ _)
  -- the check, row by row
  have hdom : ∀ i, ∑ j, (if i = j then 0 else |R i j|) ≤ R i i := by
    intro i
    have hi' := (List.all_eq_true.mp h) i (List.mem_finRange i)
    have hrow := toReal_le_of_le hi'
    have hsum := sum_le_sumUp (fun j => if j = i then (zero : 𝕋)
      else maximum (hi i j) (neg (lo i j)))
    -- each `|Rᵢⱼ|` below its rounded bound
    have hcmp : ∑ j, (if i = j then 0 else |R i j|)
        ≤ ∑ j, toReal (if j = i then (zero : 𝕋) else maximum (hi i j) (neg (lo i j))) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp [toReal_zero]
      · rw [if_neg hij, if_neg (Ne.symm hij)]
        exact habs i j
    linarith [(hbr i i).1]
  -- `R` dominant, so positive semi-definite, and `Xr = R + Lr Lrᵀ`
  have hRpsd : R.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · ext i j
      simp only [conjTranspose_apply, star_trivial]
      exact (hsymR i j).symm
    · simpa using Real.Ellipsoid.quad_nonneg_of_dominant R hsymR hdom v
  have hLpsd : (Lr * Lrᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose Lr
  have hsplit : Xr = R + Lr * Lrᵀ := by rw [hR, sub_add_cancel]
  rw [hsplit]
  exact hRpsd.add hLpsd

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
