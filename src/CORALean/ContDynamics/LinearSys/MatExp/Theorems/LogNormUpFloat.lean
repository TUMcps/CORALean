module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.LogNormUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaleConjExp
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormLeOfSumAbsLe

@[expose] public section

/-!
# `MatExp.logNormUpFloat` bounds the balanced growth of `e^{tA}`

`S⁻¹ e^{tA} S = e^{t S⁻¹ A S}` (`MatExp.scaleConj_exp`), and every row of `S⁻¹ A S` has the
diagonal entry `a_jj` and the off-diagonal absolute entries `|a_jk| s_k / s_j`, whose rounded-up
sum with `a_jj` the float bounds; `MatExp.norm_exp_smul_le_logNorm` then gives `e^{tμ}`.

## Inputs
* `A` – float matrix
* `s` – float scales
* `t` – time

## Hypotheses
* `hs` – the scales are positive
* `ht` – time nonnegative

## Conclusion
* `‖S⁻¹ e^{tA} S‖ ≤ e^{tμ}` for the float bound `μ`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix NormedSpace FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^{x I}` has norm at most `e^x`. -/
private theorem MatExp.aux_norm_exp_smul_one_le (x : ℝ) : -- --- CONCL ---
    ‖exp (x • (1 : Mat ℝ n n))‖ ≤ Real.exp x := by -- --- PROOF ---
  have h1 : x • (1 : Mat ℝ n n) = diagonal (fun _ => x) := by
    ext i j; by_cases h : i = j <;> simp [h]
  rw [h1, Matrix.exp_diagonal, Matrix.linfty_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos x).le).mpr fun i => ?_
  rw [Pi.exp_def, ← Real.exp_eq_exp_ℝ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]


private theorem MatExp.aux_norm_exp_smul_le_logNorm (B : Mat ℝ n n) {μ t : ℝ} (ht : 0 ≤ t)
    (hμ : ∀ j, B j j + ∑ k ∈ Finset.univ.erase j, |B j k| ≤ μ) : -- --- CONCL ---
    ‖exp (t • B)‖ ≤ Real.exp (t * μ) := by -- --- PROOF ---
  set c : ℝ := ∑ j, |B j j| with hc
  have hcj : ∀ j, |B j j| ≤ c := fun j =>
    Finset.single_le_sum (f := fun j => |B j j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set B' : Mat ℝ n n := B + c • 1 with hB'
  -- the shifted rows: a nonnegative diagonal, so each absolute sum is the bounded one plus `c`
  have hrow : ∀ j, ∑ k, |B' j k| ≤ μ + c := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hd : B' j j = B j j + c := by simp [hB']
    have hoff : ∑ k ∈ Finset.univ.erase j, |B' j k| = ∑ k ∈ Finset.univ.erase j, |B j k| := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkj : j ≠ k := fun h => (Finset.mem_erase.mp hk).1 h.symm
      simp [hB', Matrix.one_apply_ne hkj]
    have hpos : 0 ≤ B j j + c := by
      have := neg_abs_le (B j j); linarith [hcj j]
    rw [hd, abs_of_nonneg hpos, hoff]
    linarith [hμ j]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim (exp (t • B)) 0, norm_zero]
    exact (Real.exp_pos _).le
  have hμc : 0 ≤ μ + c :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hrow ⟨0, hn⟩)
  have hnorm : ‖B'‖ ≤ μ + c := Real.MatExp.norm_le_of_sum_abs_le B' hμc hrow
  -- `tB = tB' - tc I`, two commuting parts
  have hsplit : t • B = t • B' + (-(t * c)) • (1 : Mat ℝ n n) := by
    rw [hB', smul_add, smul_smul, add_assoc, ← add_smul]; simp
  have hcomm : Commute (t • B') ((-(t * c)) • (1 : Mat ℝ n n)) :=
    (Commute.one_right _).smul_right _
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm]
  refine le_trans (norm_mul_le _ _) ?_
  have h1 := Real.MatExp.norm_exp_smul_le B' ht
  have h2 := MatExp.aux_norm_exp_smul_one_le (n := n) (-(t * c))
  have h3 : Real.exp (t * ‖B'‖) ≤ Real.exp (t * (μ + c)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnorm ht)
  calc ‖exp (t • B')‖ * ‖exp ((-(t * c)) • (1 : Mat ℝ n n))‖
      ≤ Real.exp (t * (μ + c)) * Real.exp (-(t * c)) :=
        mul_le_mul (le_trans h1 h3) h2 (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (t * μ) := by rw [← Real.exp_add]; ring_nf


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.norm_scaleConj_exp_le_logNormUpFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {t : ℝ} (ht : 0 ≤ t) : -- --- CONCL ---
    ‖Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A))‖
      ≤ Real.exp (t * toReal (MatExp.logNormUpFloat A s)) := by -- --- PROOF ---
  have hs0 : ∀ i, toRealVec s i ≠ 0 := fun i => (hs i).ne'
  set B := Real.MatExp.scaleConj (toRealVec s) (toRealMat A) with hB
  have happ : ∀ j k, B j k = toReal (A j k) * toReal (s k) / toReal (s j) := by
    intro j k
    simp [hB, Real.MatExp.scaleConj, Matrix.mul_diagonal, Matrix.diagonal_mul, toRealVec,
      toRealMat]
    ring
  have hconj : Real.MatExp.scaleConj (toRealVec s) (exp (t • toRealMat A)) = exp (t • B) := by
    rw [Real.MatExp.scaleConj_exp hs0, hB]
    simp [Real.MatExp.scaleConj]
  rw [hconj]
  -- row `j`: the diagonal plus the scaled off-diagonal sum, rounded up
  refine MatExp.aux_norm_exp_smul_le_logNorm B ht fun j => ?_
  set g : Fin n → 𝕋 := fun k =>
    if k = j then zero else divUp (mulUp (absolute (A j k)) (s k)) (s j) with hg
  have hdiag : B j j = toReal (A j j) := by
    rw [happ]; field_simp [(hs j).ne']
  have hoff : ∑ k ∈ Finset.univ.erase j, |B j k| ≤ toReal (sumUp g) := by
    refine le_trans ?_ (sum_le_sumUp g)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hgj : toReal (g j) = 0 := by simp [hg, toReal_zero]
    rw [hgj, zero_add]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hsj := hs j
    have hsk := hs k
    simp only [hg, if_neg hkj]
    rw [happ, abs_div, abs_mul, abs_of_pos hsk, abs_of_pos hsj]
    have h1 := mul_le_mulUp (absolute (A j k)) (s k)
    rw [toReal_absolute] at h1
    exact le_trans (div_le_div_of_nonneg_right h1 hsj.le) (div_le_divUp _ _ hsj)
  -- the row's float bound is at most their maximum
  rw [hdiag]
  refine le_trans (le_trans (add_le_add le_rfl hoff) (add_le_addUp _ _)) ?_
  exact le_maximumOver (fun j => addUp (A j j) (sumUp fun k =>
    if k = j then zero else divUp (mulUp (absolute (A j k)) (s k)) (s j))) j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
