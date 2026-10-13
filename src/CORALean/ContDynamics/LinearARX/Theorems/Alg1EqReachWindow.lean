import CORALean.ContDynamics.LinearARX.Operations.Alg1
import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLe
import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLt
import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowEq
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Alg. 1 computes the reachable windows

[1, Thm. 2]: for `k_init ≥ p`, pass `m` of [1, Alg. 1] returns exactly the reachable
windows at `k = k_init + m p`, and so, block by block (`reachOut_eq_image_block`), the
reachable sets `Y(k) … Y(k₊)`. The loop keeps `S = Ã(k) ỹ_init ⊕ ⊕_{i=p}^{k₊} B̃ᵢ(k) Ũ(k₊-i)`:
line 13 is that invariant at `k + p` by [1, Lemma 1], and the stored `B̃ᵢ`, `i < 2p`, are
`B̃ᵢ(k)` by [1, Lemma 2] once refreshed at `k < 3p`. Then line 7 is [1, Eq. 12].

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `i = a, …, b - 1` written as the listing writes it. -/
theorem LinearARX.aux_Icc_sub_one (a b : ℕ) (hb : 0 < b) :
    Finset.Icc a (b - 1) = Finset.Ico a b := by
  ext x
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- A matrix applied to a sum of linear images of sets, exactly. -/
theorem LinearARX.aux_image_sum {n m : ℕ} (M : Mat ℝ m n) (s : Finset ℕ)
    (B : ℕ → Mat ℝ n du) (V : ℕ → Set (Vec ℝ du)) (a : Vec ℝ n) :
    (M *ᵥ ·) '' ({a} + ∑ i ∈ s, (B i *ᵥ ·) '' V i)
      = {M *ᵥ a} + ∑ i ∈ s, ((M * B i) *ᵥ ·) '' V i := by -- --- PROOF ---
  have hM : (M *ᵥ · : Vec ℝ n → Vec ℝ m) = ⇑(Matrix.mulVecLin M) := rfl
  rw [hM, Set.image_add, Set.image_singleton, Set.image_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.image_image]
  congr 1
  funext v
  rw [Matrix.mulVecLin_apply, mulVec_mulVec]

/-- The loop invariant of Alg. 1: the step, the set `S`, and the stored parameters. -/
theorem LinearARX.aux_alg1State (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) {kinit : ℕ} (hp : 0 < p) (hk : p ≤ kinit) (m : ℕ) :
    (sys.alg1State yinit U kinit m).1 = kinit + m * p ∧
    (sys.alg1State yinit U kinit m).2.1 = {sys.Aext ^ (kinit + m * p) *ᵥ yinit}
      + ∑ i ∈ Finset.Ico p (kinit + m * p + p),
          (sys.Btilde (kinit + m * p) i *ᵥ ·) '' U (kinit + m * p + p - 1 - i) ∧
    ∀ i < 2 * p,
      (sys.alg1State yinit U kinit m).2.2 i = sys.Btilde (kinit + m * p) i := by -- --- PROOF ---
  induction m with
  | zero =>
    rw [zero_mul, add_zero]
    refine ⟨rfl, ?_, fun _ _ => rfl⟩
    show {sys.Aext ^ kinit *ᵥ yinit} + ∑ i ∈ Finset.Icc p (kinit + p - 1),
      (fun x => sys.Btilde kinit i *ᵥ x) '' U (kinit + p - 1 - i) = _
    rw [LinearARX.aux_Icc_sub_one _ _ (by omega)]
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    set k := kinit + m * p with hkdef
    have hk' : kinit + (m + 1) * p = k + p := by rw [hkdef]; ring
    rw [hk']
    -- the stored parameters, refreshed or settled
    have hB : ∀ i < 2 * p, (sys.alg1State yinit U kinit (m + 1)).2.2 i = sys.Btilde (k + p) i := by
      intro i hi
      by_cases hlt : k + p < 3 * p
      · by_cases hpi : p ≤ i ∧ i ≤ 2 * p - 1
        · simp only [LinearARX.alg1State, h1, if_pos hlt, if_pos hpi]
        · simp only [LinearARX.alg1State, h1, if_pos hlt, if_neg hpi]
          rw [h3 i hi, sys.Btilde_add_of_lt k p (by omega)]
      · simp only [LinearARX.alg1State, h1, if_neg hlt]
        rw [h3 i hi, sys.Btilde_add_of_lt k p (by omega)]
    refine ⟨by simp only [LinearARX.alg1State, h1], ?_, hB⟩
    -- line 13, with the refreshed parameters
    have hS : (sys.alg1State yinit U kinit (m + 1)).2.1 = (sys.Aext ^ p *ᵥ ·) ''
        (sys.alg1State yinit U kinit m).2.1 + ∑ i ∈ Finset.Ico p (2 * p),
          (sys.Btilde (k + p) i *ᵥ ·) '' U (k + p + p - 1 - i) := by
      have hB' := hB
      simp only [LinearARX.alg1State, h1] at hB' ⊢
      rw [LinearARX.aux_Icc_sub_one _ _ (by omega)]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hB' i (Finset.mem_Ico.mp hi).2]
    rw [hS, h2, LinearARX.aux_image_sum, mulVec_mulVec, ← pow_add, add_comm p k, add_assoc]
    congr 1
    -- the old summands, moved on by `Ā_ext^p` (Lemma 1), reindexed by `p`
    have hold : ∀ i ∈ Finset.Ico p (k + p), ((sys.Aext ^ p * sys.Btilde k i) *ᵥ ·) ''
        U (k + p - 1 - i) = (sys.Btilde (k + p) ↑(i + p) *ᵥ ·) '' U (k + p + p - 1 - (i + p)) := by
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      rw [(sys.Btilde_add_of_le k p).2 (↑(i + p)) (by push_cast; omega),
        show ((↑(i + p) : ℤ) - p) = i by push_cast; ring, show k + p + p - 1 - (i + p)
          = k + p - 1 - i by omega]
    rw [Finset.sum_congr rfl hold, Finset.sum_Ico_add' (fun j : ℕ => (sys.Btilde (k + p) ↑j *ᵥ ·) ''
      U (k + p + p - 1 - j)), add_comm, two_mul,
      Finset.sum_Ico_consecutive _ (by omega : p ≤ p + p) (by omega : p + p ≤ k + p + p)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.alg1_eq_reachWindow (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    {U : ℕ → Set (Vec ℝ du)} (hU : ∀ i, (U i).Nonempty) {kinit : ℕ} (hp : 0 < p)
    (hk : p ≤ kinit) (m : ℕ) :
    sys.alg1 yinit U kinit m = sys.reachWindow yinit U (kinit + m * p) := by -- --- PROOF ---
  obtain ⟨h1, h2, h3⟩ := sys.aux_alg1State yinit U hp hk m
  simp only [LinearARX.alg1]
  rw [h1, h2, sys.reachWindow_eq yinit hU, add_assoc]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : p ≤ kinit + m * p + p), add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h3 i (by have := Finset.mem_range.mp hi; omega)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
