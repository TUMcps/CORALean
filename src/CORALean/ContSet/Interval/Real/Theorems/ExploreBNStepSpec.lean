module

public import CORALean.ContSet.Interval.Real.Operations.ExploreBNVisits
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# What line 6 of `EXPLORE BN` computes

[1, Alg. 2], lines 5-7, from the s-face `(p₁, …, p_j, *, …, *)` of the box `[0, b₁] × … × [0, bₙ]`:
`lab k` raises the coordinates `j+1, …, k` to their upper bound, and its vertex sum grows with `k`
since `b ≥ 0`. If the face's own vertex `lab j` is not above the plane, line 6's `k` is a
number between `j` and `n` with `lab k` not above the plane, and the next one above it unless
`k = n`: exactly the condition [1, Lemma 6.1] needs, `Σ_{i≤k} vᵢ ≤ α < b_{k+1} + Σ_{i≤k} vᵢ`.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
theorem Interval.exploreBN_step_spec (b : Vec ℝ n) (α : ℝ) (j : ℕ) (p : Fin n → Bool)
    (hj : j ≤ n) (hb0 : ∀ i, 0 ≤ b i)
    (hP : ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner
      (fun i => if (i : ℕ) < j then p i else false) i ≤ α) : -- --- CONCL ---
    let lab : ℕ → Fin n → Bool := fun k i => if (i : ℕ) < j then p i else decide ((i : ℕ) < k)
    let P := fun k => ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab k) i ≤ α
    let k := max j (Nat.findGreatest P n)
    (∀ m m', m ≤ m' → ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab m) i ≤
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab m') i) ∧
    j ≤ k ∧ k ≤ n ∧ P k ∧ (k < n → ¬ P (k + 1)) := by -- --- PROOF ---
  intro lab P k
  -- the vertex sums grow with `k`: a coordinate raised stays raised, and `bᵢ ≥ 0`
  have hmono : ∀ m m', m ≤ m' → ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab m) i ≤
      ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab m') i := by
    intro m m' hmm
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Interval.corner, lab]
    by_cases hij : (i : ℕ) < j
    · simp [hij]
    · by_cases him : (i : ℕ) < m
      · simp [hij, him, show (i : ℕ) < m' by omega]
      · by_cases hm' : (i : ℕ) < m' <;> simp [hij, him, hm', hb0 i]
  -- the face's own vertex is `lab j`, below the plane by assumption
  have hPj : P j := by
    have : lab j = fun i : Fin n => if (i : ℕ) < j then p i else false := by
      funext i; by_cases hij : (i : ℕ) < j <;> simp [lab, hij]
    show ∑ i, (⟨0, b⟩ : Interval (Vec ℝ n)).corner (lab j) i ≤ α
    rw [this]; exact hP
  have hle : j ≤ Nat.findGreatest P n := Nat.le_findGreatest hj hPj
  have hk : k = Nat.findGreatest P n := max_eq_right hle
  refine ⟨hmono, le_max_left _ _, ?_, ?_, ?_⟩
  · rw [hk]; exact Nat.findGreatest_le n
  · rw [hk]; exact Nat.findGreatest_spec hj hPj
  · intro hkn
    rw [hk] at hkn ⊢
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hkn

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
