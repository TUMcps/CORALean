module

public import CORALean.ContDynamics.LinearSysDT.Definitions.ReachErrorSet
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The reachable error set one step on

Eq. 24 of [1, Thm. 2] read as a recursion: `Ω_{k+1} ⊆ (A - LC) Ω_k ⊕ E W ⊕ (-LF) V`, the error
dynamics [1, Eq. 14] on sets. The proofs of [1, Thm. 6], [1, Thm. 7] and [1, Thm. 8] compare
`Ω_k` with another method's error bound through it (their Eqs. 51, 57 and 47). The `i = 0` terms
of the two sums are the new `E W`, `(-LF) V`; the others and `(A - LC)ᵏ⁺¹ Ω₀` are `A - LC`
applied to a point of `Ω_k`.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise CORALean.Real

variable {n ny nw nv : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- a sum over `i < k + 1` of points of `(M^i K) X` is `K x₀` plus `M` times such a sum over `i < k`
theorem LinearSysDT.aux_sum_succ_mem {m : ℕ} (M : Mat ℝ n n) (K : Mat ℝ n m) (X : Set (Vec ℝ m))
    (k : ℕ) (g : ℕ → Vec ℝ n)
    (hg : ∀ {i}, i ∈ Finset.range (k + 1) → g i ∈ ((M ^ i * K) *ᵥ ·) '' X) :
    ∃ z ∈ ∑ i ∈ Finset.range k, ((M ^ i * K) *ᵥ ·) '' X, ∃ x₀ ∈ X,
      ∑ i ∈ Finset.range (k + 1), g i = M *ᵥ z + K *ᵥ x₀ := by -- --- PROOF ---
  have hsucc : ∀ i, i < k → ∃ z ∈ ((M ^ i * K) *ᵥ ·) '' X, g (i + 1) = M *ᵥ z := by
    intro i hi
    obtain ⟨x, hx, hgx⟩ := hg (Finset.mem_range.mpr (by omega : i + 1 < k + 1))
    exact ⟨_, ⟨x, hx, rfl⟩, by rw [← hgx, mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']⟩
  choose! z hz hgz using hsucc
  obtain ⟨x₀, hx₀, hg0⟩ := hg (Finset.mem_range.mpr (Nat.succ_pos k))
  refine ⟨∑ i ∈ Finset.range k, z i,
    Set.finsetSum_mem_finsetSum _ _ _ fun i hi => hz i (Finset.mem_range.mp hi), x₀, hx₀, ?_⟩
  rw [Finset.sum_range_succ', mulVec_sum, ← hg0, pow_zero, Matrix.one_mul]
  congr 1
  exact Finset.sum_congr rfl fun i hi => hgz i (Finset.mem_range.mp hi)


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reachErrorSet_succ_subset (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (L : Mat ℝ n ny) (X₀ : Zonotope (Vec ℝ n)) (W : Zonotope (Vec ℝ nw))
    (V : Zonotope (Vec ℝ nv)) (k : ℕ) :
    LinearSysDT.reachErrorSet A C E F L X₀ W V (k + 1) ⊆
      ((A - L * C) *ᵥ ·) '' LinearSysDT.reachErrorSet A C E F L X₀ W V k +
        (E *ᵥ ·) '' W.construct + ((-(L * F)) *ᵥ ·) '' V.construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩, c, hc, rfl⟩
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hb
  obtain ⟨f, hf, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hc
  -- split off the `i = 0` terms, the rest being `A - LC` times a point of `Ω_k`
  obtain ⟨zg, hzg, w₀, hw₀, hgs⟩ := LinearSysDT.aux_sum_succ_mem _ _ _ k g hg
  obtain ⟨zf, hzf, v₀, hv₀, hfs⟩ := LinearSysDT.aux_sum_succ_mem _ _ _ k f hf
  refine ⟨_, ⟨_, ⟨((A - L * C) ^ k) *ᵥ a + zg + zf,
    Set.add_mem_add (Set.add_mem_add ⟨a, ha, rfl⟩ hzg) hzf, rfl⟩, _, ⟨w₀, hw₀, rfl⟩, rfl⟩,
    _, ⟨v₀, hv₀, rfl⟩, ?_⟩
  rw [hgs, hfs]
  simp only [mulVec_add, mulVec_mulVec, ← pow_succ']
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
