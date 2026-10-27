module

public import CORALean.ContDynamics.LinearARX.Operations.Alg2
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLe
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeAddOfLt
public import CORALean.ContDynamics.LinearARX.Theorems.ReachWindowExactEq
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# Alg. 2 computes the reachable windows, started at `k_init = p`

[1, Thm. 3], for `k_init = p`, the start CORA's `reach` uses: pass `m` of [1, Alg. 2]
returns exactly the reachable windows at `k = p + m p` when `Ũ(i) = Ũ_c + ũ_v(i)`. The loop
keeps `S_c = ⊕_{i<k} B̃ᵢ(k) Ũ_c`, `T_c1 = ⊕_{i=k}^{k₊} B̃ᵢ(k) Ũ_c`, `T_c2 = ⊕_{i=k}^{k₊} B̃ᵢ(k+p)
Ũ_c` (from the first pass on) and `s_v` as Alg. 1's `S` on the points, by [1, Lemma 1] and
[1, Lemma 2]. For `k_init > p` the theorem fails: `alg2_ne_reachWindowExact`.

## Inputs
* `sys` – ARX system
* `yinit` – measured first output window
* `Uc` – constant input set
* `uv` – varying input
* `m` – pass index

## Hypotheses
* `hUc` – constant input set nonempty
* `hp` – at least one lag

## Conclusion
* pass `m` returns exactly the reachable windows

## References

* [1] [L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.](../../../../../references/2023/luetzow-cdc-armax.md)
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
private theorem LinearARX.aux_Icc_pred (a b : ℕ) (hb : 0 < b) :
    Finset.Icc a (b - 1) = Finset.Ico a b := by
  ext x
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- A matrix applied to a sum of linear images of one set, exactly. -/
private theorem LinearARX.aux_image_sum_set {n m : ℕ} (M : Mat ℝ m n) (s : Finset ℕ)
    (B : ℕ → Mat ℝ n du) (V : Set (Vec ℝ du)) : -- --- CONCL ---
    (M *ᵥ ·) '' (∑ i ∈ s, (B i *ᵥ ·) '' V) = ∑ i ∈ s, ((M * B i) *ᵥ ·) '' V := by -- --- PROOF ---
  have hM : (M *ᵥ · : Vec ℝ n → Vec ℝ m) = ⇑(Matrix.mulVecLin M) := rfl
  rw [hM, Set.image_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Set.image_image]
  congr 1
  funext v
  rw [Matrix.mulVecLin_apply, mulVec_mulVec]

/-- The constant parameters moved on by `p` steps, Lemma 1 summed over a block of indices. -/
private theorem LinearARX.aux_shift_sum (sys : LinearARX 𝕋 dy du p) (k a b : ℕ) (hab : p ≤ a)
    (V : ℕ → Set (Vec ℝ du)) : -- --- CONCL ---
    ∑ i ∈ Finset.Ico a b, ((sys.Aext ^ p * sys.Btilde k i) *ᵥ ·) '' V i
      = ∑ i ∈ Finset.Ico (a + p) (b + p),
        (sys.Btilde (k + p) i *ᵥ ·) '' V (i - p) := by -- --- PROOF ---
  rw [← Finset.sum_Ico_add' (fun j : ℕ => (sys.Btilde (k + p) j *ᵥ ·) '' V (j - p))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_Ico.mp hi
  rw [(sys.Btilde_add_of_le k p).2 (↑(i + p)) (by push_cast; omega),
    show ((↑(i + p) : ℤ) - p) = i by push_cast; ring, Nat.add_sub_cancel]

/-- The same for the points of `s_v`. -/
private theorem LinearARX.aux_shift_sum_vec (sys : LinearARX 𝕋 dy du p) (k a b : ℕ) (hab : p ≤ a)
    (v : ℕ → Vec ℝ du) : -- --- CONCL ---
    ∑ i ∈ Finset.Ico a b, (sys.Aext ^ p * sys.Btilde k i) *ᵥ v i
      = ∑ i ∈ Finset.Ico (a + p) (b + p), sys.Btilde (k + p) i *ᵥ v (i - p) := by -- --- PROOF ---
  rw [← Finset.sum_Ico_add' (fun j : ℕ => sys.Btilde (k + p) j *ᵥ v (j - p))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_Ico.mp hi
  rw [(sys.Btilde_add_of_le k p).2 (↑(i + p)) (by push_cast; omega),
    show ((↑(i + p) : ℤ) - p) = i by push_cast; ring, Nat.add_sub_cancel]

/-- The loop invariant of Alg. 2, started at `k_init = p`. -/
private theorem LinearARX.aux_alg2State_inv (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (Uc : Set (Vec ℝ du)) (uv : ℕ → Vec ℝ du) (hp : 0 < p) (m : ℕ) : -- --- CONCL ---
    (sys.step_alg2State yinit Uc uv p m).1 = p + m * p ∧
    (sys.step_alg2State yinit Uc uv p m).2.1
      = ∑ i ∈ Finset.range (p + m * p), (sys.Btilde (p + m * p) i *ᵥ ·) '' Uc ∧
    (sys.step_alg2State yinit Uc uv p m).2.2.1
      = ∑ i ∈ Finset.Ico (p + m * p) (p + m * p + p), (sys.Btilde (p + m * p) i *ᵥ ·) '' Uc ∧
    (0 < m → (sys.step_alg2State yinit Uc uv p m).2.2.2.1
      = ∑ i ∈ Finset.Ico (p + m * p) (p + m * p + p),
          (sys.Btilde (p + m * p + p) i *ᵥ ·) '' Uc) ∧
    (sys.step_alg2State yinit Uc uv p m).2.2.2.2.1 = sys.Aext ^ (p + m * p) *ᵥ yinit
      + ∑ i ∈ Finset.Ico p (p + m * p + p),
          sys.Btilde (p + m * p) i *ᵥ uv (p + m * p + p - 1 - i) ∧
    ∀ i < 2 * p,
      (sys.step_alg2State yinit Uc uv p m).2.2.2.2.2 i =
        sys.Btilde (p + m * p) i := by -- --- PROOF ---
  induction m with
  | zero =>
    rw [zero_mul, add_zero]
    refine ⟨rfl, rfl, ?_, fun h => absurd h (lt_irrefl 0), ?_, fun _ _ => rfl⟩
    · show ∑ i ∈ Finset.Icc p (p + p - 1), (fun x => sys.Btilde p i *ᵥ x) '' Uc = _
      rw [LinearARX.aux_Icc_pred _ _ (by omega)]
    · show sys.Aext ^ p *ᵥ yinit + ∑ i ∈ Finset.Icc p (p + p - 1),
        sys.Btilde p i *ᵥ uv (p + p - 1 - i) = _
      rw [LinearARX.aux_Icc_pred _ _ (by omega)]
  | succ m ih =>
    obtain ⟨h1, hSc, hTc1, hTc2, hsv, hB⟩ := ih
    set k := p + m * p with hkdef
    have hk' : p + (m + 1) * p = k + p := by rw [hkdef]; ring
    rw [hk']
    -- the stored parameters, refreshed or settled, as in Alg. 1
    have hB' : ∀ i < 2 * p,
        (sys.step_alg2State yinit Uc uv p (m + 1)).2.2.2.2.2 i = sys.Btilde (k + p) i := by
      intro i hi
      by_cases hlt : k + p < 3 * p
      · by_cases hpi : p ≤ i ∧ i ≤ 2 * p - 1
        · simp only [LinearARX.step_alg2State, h1, if_pos hlt, if_pos hpi]
        · simp only [LinearARX.step_alg2State, h1, if_pos hlt, if_neg hpi]
          rw [hB i hi, sys.Btilde_add_of_lt k p (by omega)]
      · simp only [LinearARX.step_alg2State, h1, if_neg hlt]
        rw [hB i hi, sys.Btilde_add_of_lt k p (by omega)]
    -- the second block's new share: the refreshed window's inputs at the first pass, else the old
    set ph := if k + p = p + p then ∑ i ∈ Finset.Icc (k + p - p) (k + p + p - 1 - p),
        ((sys.step_alg2State yinit Uc uv p (m + 1)).2.2.2.2.2 i *ᵥ ·) '' Uc
      else (sys.step_alg2State yinit Uc uv p m).2.2.2.1 with hph
    -- `T_c2` before line 22: assigned in the first pass, carried after
    have hmid : ph
        = ∑ i ∈ Finset.Ico k (k + p), (sys.Btilde (k + p) i *ᵥ ·) '' Uc := by
      rw [hph]
      by_cases hm : m = 0
      · have hkp : k = p := by rw [hkdef, hm, zero_mul, add_zero]
        rw [if_pos (by omega), show k + p - p = k by omega,
          show k + p + p - 1 - p = (k + p) - 1 by omega, LinearARX.aux_Icc_pred _ _ (by omega)]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hB' i (by have := Finset.mem_Ico.mp hi; omega)]
      · rw [if_neg (by have := Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero hm); omega),
          hTc2 (by omega)]
    refine ⟨by simp only [LinearARX.step_alg2State, h1], ?_, ?_, fun _ => ?_, ?_, hB'⟩
    · -- line 20, by Lemma 2
      have e : (sys.step_alg2State yinit Uc uv p (m + 1)).2.1 =
          (sys.step_alg2State yinit Uc uv p m).2.1
          + ph := by
        simp only [LinearARX.step_alg2State, h1, hph]
      rw [e, hmid, hSc, ← Finset.sum_range_add_sum_Ico _ (by omega : k ≤ k + p)]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [sys.Btilde_add_of_lt k p (by have := Finset.mem_range.mp hi; omega)]
    · -- line 21, by Lemma 1
      have e : (sys.step_alg2State yinit Uc uv p (m + 1)).2.2.1
          = (sys.Aext ^ p *ᵥ ·) '' (sys.step_alg2State yinit Uc uv p m).2.2.1 := by
        simp only [LinearARX.step_alg2State, h1]
      rw [e, hTc1, LinearARX.aux_image_sum_set,
        sys.aux_shift_sum k k (k + p) (by omega) (fun _ => Uc)]
    · -- line 22, by Lemma 1 at `k + p`
      have e : (sys.step_alg2State yinit Uc uv p (m + 1)).2.2.2.1 = (sys.Aext ^ p *ᵥ ·) '' ph := by
        simp only [LinearARX.step_alg2State, h1, hph]
      rw [e, hmid, LinearARX.aux_image_sum_set,
        sys.aux_shift_sum (k + p) k (k + p) (by omega) (fun _ => Uc)]
    · -- line 23, as line 13 of Alg. 1
      have e : (sys.step_alg2State yinit Uc uv p (m + 1)).2.2.2.2.1
          = sys.Aext ^ p *ᵥ (sys.step_alg2State yinit Uc uv p m).2.2.2.2.1
            + ∑ i ∈ Finset.Icc p (2 * p - 1),
              (sys.step_alg2State yinit Uc uv p (m + 1)).2.2.2.2.2 i *ᵥ uv (k + p + p - 1 - i) := by
        simp only [LinearARX.step_alg2State, h1]
      rw [e, hsv, mulVec_add, mulVec_mulVec, ← pow_add, add_comm p k, mulVec_sum]
      simp only [mulVec_mulVec]
      rw [sys.aux_shift_sum_vec k p (k + p) le_rfl (fun j => uv (k + p - 1 - j)),
        LinearARX.aux_Icc_pred _ _ (by omega), add_assoc]
      congr 1
      have hold : ∀ i ∈ Finset.Ico (p + p) (k + p + p),
          sys.Btilde (k + p) i *ᵥ uv (k + p - 1 - (i - p))
            = sys.Btilde (k + p) i *ᵥ uv (k + p + p - 1 - i) := by
        intro i hi
        rw [show k + p - 1 - (i - p) = k + p + p - 1 - i by
          have := Finset.mem_Ico.mp hi; omega]
      rw [Finset.sum_congr rfl hold, add_comm, two_mul,
        Finset.sum_congr rfl fun i hi => by rw [hB' i (by have := Finset.mem_Ico.mp hi; omega)],
        Finset.sum_Ico_consecutive _ (by omega : p ≤ p + p) (by omega : p + p ≤ k + p + p)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.alg2_eq_reachWindowExact (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    {Uc : Set (Vec ℝ du)} (hUc : Uc.Nonempty) (uv : ℕ → Vec ℝ du) (hp : 0 < p)
    (m : ℕ) : -- --- CONCL ---
    sys.alg2 yinit Uc uv p m
      = sys.reachWindowExact yinit (fun i => Uc + {uv i}) (p + m * p) := by -- --- PROOF ---
  obtain ⟨h1, hSc, hTc1, -, hsv, hB⟩ := sys.aux_alg2State_inv yinit Uc uv hp m
  set k := p + m * p
  simp only [LinearARX.alg2]
  rw [h1, hSc, hTc1, hsv,
    sys.reachWindowExact_eq yinit (fun i => hUc.add (Set.singleton_nonempty _)),
    Finset.sum_range_add_sum_Ico _ (by omega : k ≤ k + p)]
  -- each input set splits into its constant part and its point
  have hsplit : ∀ i ∈ Finset.range (k + p), (sys.Btilde k i *ᵥ ·) '' (Uc + {uv (k + p - 1 - i)})
      = (sys.Btilde k i *ᵥ ·) '' Uc + {sys.Btilde k i *ᵥ uv (k + p - 1 - i)} := by
    intro i _
    have hM : (sys.Btilde k i *ᵥ · : Vec ℝ du → Vec ℝ (p * dy))
        = ⇑(Matrix.mulVecLin (sys.Btilde k i)) := rfl
    rw [hM, Set.image_add, Set.image_singleton, Matrix.mulVecLin_apply]
  -- the point part: lines 7, 10 and 23 add up to `Ã(k) ỹ_init + ∑ B̃ᵢ(k) ũ_v(k₊ - i)`
  have hlow : ∀ i ∈ Finset.range p, sys.step_alg2State yinit Uc uv p m |>.2.2.2.2.2 i *ᵥ
      uv (k + p - 1 - i) = sys.Btilde k i *ᵥ uv (k + p - 1 - i) := by
    intro i hi
    rw [hB i (by have := Finset.mem_range.mp hi; omega)]
  have hv : sys.Aext ^ k *ᵥ yinit
      + ∑ i ∈ Finset.Ico p (k + p), sys.Btilde k i *ᵥ uv (k + p - 1 - i)
      + ∑ i ∈ Finset.range p, sys.Btilde k i *ᵥ uv (k + p - 1 - i)
      = sys.Aext ^ k *ᵥ yinit
        + ∑ i ∈ Finset.range (k + p), sys.Btilde k i *ᵥ uv (k + p - 1 - i) := by
    rw [← Finset.sum_range_add_sum_Ico (fun i : ℕ => sys.Btilde k i *ᵥ uv (k + p - 1 - i))
      (by omega : p ≤ k + p)]
    abel
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Set.finsetSum_singleton,
    Finset.sum_congr rfl hlow, hv, ← Set.singleton_add_singleton]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
