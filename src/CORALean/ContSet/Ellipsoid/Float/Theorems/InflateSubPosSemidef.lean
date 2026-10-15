module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Inflate
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QuadNonnegOfDominant
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The inflated matrix dominates every symmetric matrix of its interval

For a symmetric real `X` inside the interval matrix, `inflate - X` is symmetric, has off-diagonal
entries in `[0, w]`, `w` the bracket's width, and diagonal entries at least the sum of their
row's widths: diagonally dominant, so positive semi-definite (`quad_nonneg_of_dominant`).
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

/-- `inflate X - X'` is positive semi-definite for every symmetric `X'` in `X`. -/
theorem Ellipsoid.inflate_sub_posSemidef {X : Interval (Mat 𝕋 n n)} {Xr : Mat ℝ n n}
    (hX : ∀ i j, toReal (X.inf i j) ≤ Xr i j ∧ Xr i j ≤ toReal (X.sup i j))
    (hsym : ∀ i j, Xr i j = Xr j i) :
    (toRealMat (Ellipsoid.inflate X) - Xr).PosSemidef := by -- --- PROOF ---
  set D : Mat ℝ n n := toRealMat (Ellipsoid.inflate X) - Xr with hD
  -- the bracket of entry `(i, j)`, read at the ordered pair
  set w : Fin n → Fin n → 𝕋 := fun i j =>
    if i ≤ j then subUp (X.sup i j) (X.inf i j) else subUp (X.sup j i) (X.inf j i) with hw
  have hInf : ∀ i j, Ellipsoid.inflate X i j
      = if i = j then addUp (if i ≤ i then X.sup i i else X.sup i i)
          (sumUp fun l => if l = i then zero else w i l)
        else if i ≤ j then X.sup i j else X.sup j i := fun _ _ => rfl
  -- off the diagonal, `0 ≤ D i j ≤ w i j`
  have hoff : ∀ i j, i ≠ j → 0 ≤ D i j ∧ D i j ≤ toReal (w i j) := by
    intro i j hij
    simp only [hD, Matrix.sub_apply, toRealMat, hInf, if_neg hij, hw]
    by_cases hle : i ≤ j
    · simp only [if_pos hle]
      have h1 := hX i j
      have h2 := sub_le_subUp (X.sup i j) (X.inf i j)
      constructor <;> linarith [h1.1, h1.2]
    · simp only [if_neg hle]
      have h1 := hX j i
      have h2 := sub_le_subUp (X.sup j i) (X.inf j i)
      rw [hsym i j]
      constructor <;> linarith [h1.1, h1.2]
  -- symmetric, as `inflate` mirrors and `Xr` is symmetric
  have hsymD : ∀ i j, D i j = D j i := by
    intro i j
    simp only [hD, Matrix.sub_apply, toRealMat, hInf, hsym i j]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [if_pos h.le, if_neg (not_le.2 h)]
      · rw [if_neg (not_le.2 h), if_pos h.le]
  -- the diagonal covers the row
  have hdom : ∀ i, ∑ j, (if i = j then 0 else |D i j|) ≤ D i i := by
    intro i
    have hsum : ∑ j, (if i = j then 0 else |D i j|)
        ≤ ∑ j, toReal (if j = i then (zero : 𝕋) else w i j) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp [toReal_zero]
      · rw [if_neg hij, if_neg (Ne.symm hij), abs_of_nonneg (hoff i j hij).1]
        exact (hoff i j hij).2
    -- the diagonal entry is the upper bound plus the rounded-up row sum
    have hup := sum_le_sumUp (fun j => if j = i then (zero : 𝕋) else w i j)
    have hadd := add_le_addUp (X.sup i i) (sumUp fun j => if j = i then (zero : 𝕋) else w i j)
    have hdiag : D i i = toReal (addUp (X.sup i i)
        (sumUp fun j => if j = i then (zero : 𝕋) else w i j)) - Xr i i := by
      simp only [hD, Matrix.sub_apply, toRealMat, hInf, if_true, le_refl]
    rw [hdiag]
    linarith [(hX i i).2]
  -- symmetric and diagonally dominant, so positive semi-definite
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · ext i j
    simp only [conjTranspose_apply, star_trivial]
    exact (hsymD i j).symm
  · simpa using Real.Ellipsoid.quad_nonneg_of_dominant D hsymD hdom v

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
