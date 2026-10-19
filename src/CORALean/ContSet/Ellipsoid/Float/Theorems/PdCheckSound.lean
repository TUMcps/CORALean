module

public import CORALean.ContSet.Ellipsoid.Float.Operations.PdCheck
public import CORALean.ContSet.Ellipsoid.Real.Theorems.QuadNonnegOfDominant
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# A passed `pdCheck` makes every symmetric matrix of the interval positive definite

`R = X' - L Lᵀ` lies entrywise between the check's two roundings, so its off-diagonal magnitudes
are below the rounded-up maxima and its diagonal above the lower bounds: strictly diagonally
dominant, by some `ε > 0` in every row, and symmetric with `X'`; `R - ε I` is then diagonally
dominant (`quad_nonneg_of_dominant`), so `vᵀ R v ≥ ε ‖v‖² > 0`; and `X' = R + L Lᵀ`.

## Inputs
* `X` – interval matrix
* `L` – factor
* `Xr` – symmetric real matrix

## Hypotheses
* `h` – `pdCheck` returns `true`
* `hX` – `Xr` entrywise in `X`
* `hsym` – `Xr` symmetric

## Conclusion
* `Xr` is positive definite
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

/-- A passed check makes every symmetric matrix of `X` positive definite. -/
theorem Ellipsoid.posDef_of_pdCheck {X : Interval (Mat 𝕋 n n)} {L : Mat 𝕋 n n}
    (h : Ellipsoid.pdCheck X L = true) {Xr : Mat ℝ n n}
    (hX : ∀ i j, toReal (X.inf i j) ≤ Xr i j ∧ Xr i j ≤ toReal (X.sup i j))
    (hsym : ∀ i j, Xr i j = Xr j i) : Xr.PosDef := by -- --- PROOF ---
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
  -- the check, row by row: a positive slack
  have hslack : ∀ i, ∑ j, (if i = j then 0 else |R i j|) < R i i := by
    intro i
    have hi' := (List.all_eq_true.mp h) i (List.mem_finRange i)
    have hrow := toReal_lt_of_ltStrict hi'
    have hsum := sum_le_sumUp (fun j => if j = i then (zero : 𝕋)
      else maximum (hi i j) (neg (lo i j)))
    have hcmp : ∑ j, (if i = j then 0 else |R i j|)
        ≤ ∑ j, toReal (if j = i then (zero : 𝕋) else maximum (hi i j) (neg (lo i j))) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp [toReal_zero]
      · rw [if_neg hij, if_neg (Ne.symm hij)]
        exact habs i j
    linarith [(hbr i i).1]
  have hRpd : R.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j
      simp only [conjTranspose_apply, star_trivial]
      exact (hsymR i j).symm
    -- the least slack `ε`, and `R - ε I` dominant
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      obtain ⟨i, -⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ i⟩
    set ε := Finset.univ.inf' hne fun i => R i i - ∑ j, (if i = j then 0 else |R i j|) with hε
    have hεpos : 0 < ε := by
      rw [hε, Finset.lt_inf'_iff]
      exact fun i _ => sub_pos.mpr (hslack i)
    -- `R - ε I` stays symmetric and dominant
    set R' : Mat ℝ n n := R - ε • 1 with hR'
    have hsymR' : ∀ i j, R' i j = R' j i := fun i j => by
      simp only [hR', Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hsymR i j, eq_comm]
    have hdomR' : ∀ i, ∑ j, (if i = j then 0 else |R' i j|) ≤ R' i i := by
      intro i
      have hεi : ε ≤ R i i - ∑ j, (if i = j then 0 else |R i j|) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have hoff : ∑ j, (if i = j then 0 else |R' i j|) = ∑ j, (if i = j then 0 else |R i j|) :=
        Finset.sum_congr rfl fun j _ => by
          by_cases hij : i = j
          · simp [hij]
          · simp [hR', hij, Matrix.one_apply_ne hij]
      rw [hoff]
      simp only [hR', Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one]
      linarith
    -- `vᵀ R v = vᵀ R' v + ε ‖v‖²`, the first nonnegative and the second positive
    have hq := Real.Ellipsoid.quad_nonneg_of_dominant R' hsymR' hdomR' v
    have hRR' : R = R' + ε • 1 := by rw [hR', sub_add_cancel]
    have hsplitv : v ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (R' *ᵥ v) + ε * (v ⬝ᵥ v) := by
      nth_rewrite 1 [hRR']
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
    have hvv : 0 < v ⬝ᵥ v := by
      rw [dotProduct_self]
      have h0 : ‖v‖₂ ≠ 0 := fun h0 => hv (funext fun i =>
        abs_nonpos_iff.mp (le_trans (abs_le_norm₂ v i) h0.le))
      positivity
    simp only [star_trivial]
    rw [hsplitv]
    nlinarith
  have hLpsd : (Lr * Lrᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose Lr
  have hsplit : Xr = R + Lr * Lrᵀ := by rw [hR, sub_add_cancel]
  rw [hsplit]
  exact hRpd.add_posSemidef hLpsd

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
