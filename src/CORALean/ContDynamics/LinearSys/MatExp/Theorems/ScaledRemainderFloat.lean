module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatLeScaled
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderBoundNonneg
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `MatExp.scaledRemainderFloat` bounds `E(r,η)` entry by entry

Every rounded-up entry of `r N` is at least the real one, so the rounded-up norm bounds `‖r N‖`
(the `l∞` norm is monotone in the absolute values of the entries); the certified test gives
`‖r N‖/(η+2) ≤ 1/2`, under which the float scalar bound is above the real one, and each
rounded-up `(s_j / s_k) τ` is above `(s_j / s_k)` times it. `Real.MatExp.expRemainderMat_le_scaled`
closes the bound.

## Inputs
* `A` – float system matrix
* `s` – float scales
* `r` – float step length
* `η` – Taylor order

## Hypotheses
* `hs` – the scales are positive
* `hr` – the step length is nonnegative

## Conclusion
* every entry of `E(r,η)` is at most the entry of a returned `W`
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The `l∞` norm is monotone in the absolute values of the entries. -/
private theorem MatExp.aux_norm_le_of_abs_le {X Y : Mat ℝ n n}
    (h : ∀ i j, |X i j| ≤ Y i j) : -- --- CONCL ---
    ‖X‖ ≤ ‖Y‖ := by -- --- PROOF ---
  have hnn : ∀ i j, ‖X i j‖₊ ≤ ‖Y i j‖₊ := fun i j => by
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact le_trans (h i j) (le_abs_self _)
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  exact_mod_cast Finset.sup_mono_fun fun i _ => Finset.sum_le_sum fun j _ => hnn i j


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expRemainderMat_le_scaledRemainderFloat (A : Mat 𝕋 n n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {r : 𝕋} (hr : 0 ≤ toReal r) (η : ℕ) : -- --- CONCL ---
    ∀ W ∈ MatExp.scaledRemainderFloat A s r η, ∀ j k,
      Real.MatExp.expRemainderMat (toRealMat A) (toReal r) η j k
        ≤ toReal (W j k) := by -- --- PROOF ---
  intro W hW j k
  rw [Option.mem_def] at hW
  set N : Mat 𝕋 n n := fun j k => mulUp (divUp (mulUp (absolute (A j k)) (s k)) (s j)) r
    with hN
  set nrm := MatExp.normUpperBound (Interval.point N) with hnrm
  unfold MatExp.scaledRemainderFloat at hW
  simp only [← hN, ← hnrm] at hW
  split_ifs at hW with htest
  simp only [Option.some.injEq, Interval.materialiseMat_eq, Interval.point] at hW
  subst hW
  -- the real scaled matrix and its rounded-up entries
  set Nr : Mat ℝ n n := Matrix.of fun j k => |toRealMat A j k| * toReal (s k) / toReal (s j)
    with hNr
  -- each rounded-up entry is above the real one
  have hentry : ∀ a b, |(toReal r • Nr) a b| ≤ toReal (N a b) := by
    intro a b
    have hsa := hs a
    have hsb := hs b
    have h0 : 0 ≤ |toReal (A a b)| * toReal (s b) / toReal (s a) := by positivity
    rw [Matrix.smul_apply, smul_eq_mul, hNr, Matrix.of_apply, toRealMat,
      abs_of_nonneg (mul_nonneg hr h0)]
    have h1 := mul_le_mulUp (absolute (A a b)) (s b)
    rw [toReal_absolute] at h1
    have h2 := div_le_divUp (mulUp (absolute (A a b)) (s b)) (s a) hsa
    have h3 := mul_le_mulUp (divUp (mulUp (absolute (A a b)) (s b)) (s a)) r
    have h12 : |toReal (A a b)| * toReal (s b) / toReal (s a)
        ≤ toReal (divUp (mulUp (absolute (A a b)) (s b)) (s a)) :=
      le_trans (div_le_div_of_nonneg_right h1 hsa.le) h2
    calc toReal r * (|toReal (A a b)| * toReal (s b) / toReal (s a))
        ≤ toReal r * toReal (divUp (mulUp (absolute (A a b)) (s b)) (s a)) :=
          mul_le_mul_of_nonneg_left h12 hr
      _ = toReal (divUp (mulUp (absolute (A a b)) (s b)) (s a)) * toReal r := mul_comm _ _
      _ ≤ toReal (N a b) := h3
  -- the norm bound
  have hnorm : ‖toReal r • Nr‖ ≤ toReal nrm := by
    refine le_trans (MatExp.aux_norm_le_of_abs_le (Y := (Interval.point N).nominal.absMax)
      fun a b => ?_) (MatExp.norm_absMax_le_normUpperBound _)
    refine le_trans (hentry a b) ?_
    simp only [Real.Interval.absMax, Interval.nominal, Interval.point, RealImage.realImage,
      toRealMat]
    exact le_trans (le_abs_self _) (le_max_left _ _)
  -- the certified test: `‖r N‖/(η+2) ≤ 1/2`
  have hnn : 0 ≤ toReal nrm := le_trans (norm_nonneg _) hnorm
  have hε : toReal nrm / ((η : ℝ) + 2) ≤ 1 / 2 := by
    have ht := toReal_le_of_le htest
    have hadd := add_le_addUp nrm nrm
    have hns := nsmulDown_le (η + 2) (one : 𝕋)
    rw [toReal_one, mul_one] at hns
    push_cast at hns
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hε' : ‖toReal r • Nr‖ / ((η : ℝ) + 2) ≤ 1 / 2 :=
    le_trans (div_le_div_of_nonneg_right hnorm (by positivity)) hε
  have hlt : ‖toReal r • Nr‖ / ((η : ℝ) + 2) < 1 := by linarith
  -- the scalar bound and its rounded-up scaling
  have hτ := MatExp.expRemainderBound_le η hnorm hnn hε
  have hτ0 := Real.MatExp.expRemainderBound_nonneg η hε'
  have hreal := Real.MatExp.expRemainderMat_le_scaled (toRealMat A) (toReal r) η hs hlt j k
  have hsk := hs k
  have hq := div_le_divUp (s j) (s k) hsk
  have hq0 : 0 ≤ toReal (s j) / toReal (s k) := div_nonneg (hs j).le hsk.le
  refine le_trans hreal (le_trans ?_ (mul_le_mulUp _ _))
  exact mul_le_mul hq hτ hτ0 (le_trans hq0 hq)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
