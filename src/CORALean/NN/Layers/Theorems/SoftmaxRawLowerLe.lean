module

public import CORALean.NN.Layers.Operations.SoftmaxRawLower
public import CORALean.NN.Layers.Theorems.Real.RawLeSoftmax
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.SumEraseLeSumOffUp

@[expose] public section

/-!
# Softmax above its rounded raw lower bound

`Real.raw_le_softmax` at the box the stored bounds denote. Where `softmaxExpInRange` holds, each
`expUp`'s hypothesis is discharged by the comparison with `expUpLimit k`; where it does not, the
bound is zero and `softmax_nonneg` is all that is needed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   08-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_expUpLimit_le (k : ℕ) :
    toReal (expUpLimit (𝕋 := 𝕋) k) ≤ 2 ^ k / 2 := by -- --- PROOF ---
  induction k with
  | zero => rw [expUpLimit, toReal_half, toReal_one]; norm_num
  | succ k ih =>
    rw [expUpLimit, pow_succ]
    have := addDown_le_add (expUpLimit (𝕋 := 𝕋) k) (expUpLimit k)
    linarith

theorem aux_softmaxExpInRange (k : ℕ) (I : Interval (Vec 𝕋 n)) {i j : Fin n}
    (h : softmaxExpInRange k I i = true) (hj : j ≠ i) :
    Real.exp (toReal (I.sup j) - toReal (I.inf i))
      ≤ toReal (expUp k (subUp (I.sup j) (I.inf i))) := by -- --- PROOF ---
  have hall := List.all_eq_true.mp h j (List.mem_finRange j)
  rw [Bool.or_eq_true, decide_eq_true_eq] at hall
  have hle : le (subUp (I.sup j) (I.inf i)) (expUpLimit k) = true := by
    rcases hall with h1 | h1
    · exact absurd h1 hj
    · exact h1
  refine le_trans (Real.exp_le_exp.mpr (sub_le_subUp _ _)) ?_
  exact le_expUp_of_le k _ _ (aux_expUpLimit_le k) hle

theorem aux_one_add_sum_le_softmaxDenomUp (k : ℕ) (I : Interval (Vec 𝕋 n)) {i : Fin n}
    (h : softmaxExpInRange k I i = true) :
    1 + ∑ j ∈ Finset.univ.erase i, Real.exp (toReal (I.sup j) - toReal (I.inf i))
      ≤ toReal (softmaxDenomUp k I i) := by -- --- PROOF ---
  have hsum := sum_erase_le_sumOffUp i fun j => expUp k (subUp (I.sup j) (I.inf i))
  have hterm : ∑ j ∈ Finset.univ.erase i, Real.exp (toReal (I.sup j) - toReal (I.inf i))
      ≤ ∑ j ∈ Finset.univ.erase i, toReal (expUp k (subUp (I.sup j) (I.inf i))) :=
    Finset.sum_le_sum fun j hj => aux_softmaxExpInRange k I h (Finset.ne_of_mem_erase hj)
  have hadd := add_le_addUp (one : 𝕋) (sumOffUp i fun j => expUp k (subUp (I.sup j) (I.inf i)))
  rw [toReal_one] at hadd
  rw [softmaxDenomUp]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Below `softmax` at every point of the box. -/
theorem softmaxRawLower_le (k : ℕ) (I : Interval (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : ∀ i, toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i)) (i : Fin n) :
    toReal (softmaxRawLower k I i) ≤ Real.softmax x i := by -- --- PROOF ---
  unfold softmaxRawLower
  split_ifs with h
  · have hD := aux_one_add_sum_le_softmaxDenomUp k I h
    have hS : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase i,
        Real.exp (toReal (I.sup j) - toReal (I.inf i)) :=
      Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
    have hpos : 0 < toReal (softmaxDenomUp k I i) := by linarith
    have h1 := divDown_le_div (one : 𝕋) (softmaxDenomUp k I i) hpos
    rw [toReal_one] at h1
    have hraw := Real.raw_le_softmax (lo := fun i => toReal (I.inf i))
      (hi := fun i => toReal (I.sup i)) hx i
    rw [inv_eq_one_div] at hraw
    refine le_trans h1 (le_trans ?_ hraw)
    exact one_div_le_one_div_of_le (by linarith) hD
  · rw [toReal_zero]
    exact Real.softmax_nonneg x i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
