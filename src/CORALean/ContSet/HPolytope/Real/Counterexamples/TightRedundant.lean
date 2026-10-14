module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `[1, Sec. 4.1 (support vector)]`: a halfspace tight at a support vector can still be redundant

The paper speeds up [1, Eq. 1]: when the `j`-th halfspace is redundant, the support vector `ν`
of the remaining polytope along its normal is a vertex, and "all halfspaces `k ≠ j` are
non-redundant, for which `A(k,·) ν = b(k)` holds". The unit square with the extra rows
`x + y ≤ 2` and `x + y ≤ 3` is a counterexample: `x + y ≤ 3` is redundant, its support vector is
the corner `(1, 1)`, and `x + y ≤ 2` is tight there yet redundant as well. A face of a polytope
can lie on a halfspace's boundary without that halfspace defining it.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.tight_redundant_counterexample :
    ∃ (A : Mat ℝ 6 2) (b : Vec ℝ 6) (j k : Fin 6) (ν : Vec ℝ 2), k ≠ j ∧
      {x | ∀ i, i ≠ j → (A *ᵥ x) i ≤ b i} = (HPolytope.ineqs A b).construct ∧
      ν ∈ {x | ∀ i, i ≠ j → (A *ᵥ x) i ≤ b i} ∧
      (∀ x ∈ {x | ∀ i, i ≠ j → (A *ᵥ x) i ≤ b i}, (A *ᵥ x) j ≤ (A *ᵥ ν) j) ∧
      (A *ᵥ ν) k = b k ∧
      {x | ∀ i, i ≠ k → (A *ᵥ x) i ≤ b i} = (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  let A : Mat ℝ 6 2 := !![1, 0; 0, 1; 1, 1; -1, 0; 0, -1; 1, 1]
  let b : Vec ℝ 6 := ![1, 1, 2, 0, 0, 3]
  -- the rows, read off
  have hA : ∀ x : Vec ℝ 2,
      A *ᵥ x = ![x 0, x 1, x 0 + x 1, -x 0, -x 1, x 0 + x 1] := by
    intro x
    funext i
    fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_two]
  -- every row other than `x + y ≤ 2` and `x + y ≤ 3` is the unit square
  have hsq : ∀ x : Vec ℝ 2, (∀ i : Fin 6, i ≠ 2 → i ≠ 5 → (A *ᵥ x) i ≤ b i) →
      x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ -x 0 ≤ 0 ∧ -x 1 ≤ 0 := by
    intro x h
    have h0 := h 0 (by simp) (by simp)
    have h1 := h 1 (by simp) (by simp)
    have h3 := h 3 (by simp) (by simp)
    have h4 := h 4 (by simp) (by simp)
    simp only [hA] at h0 h1 h3 h4
    exact ⟨h0, h1, h3, h4⟩
  -- the square satisfies every row
  have hall : ∀ x : Vec ℝ 2, x 0 ≤ 1 → x 1 ≤ 1 → -x 0 ≤ 0 → -x 1 ≤ 0 →
      ∀ i, (A *ᵥ x) i ≤ b i := by
    intro x h0 h1 h3 h4 i
    rw [hA]
    fin_cases i <;> simp [b] <;> linarith
  have hdrop : ∀ k : Fin 6, k = 2 ∨ k = 5 →
      {x | ∀ i, i ≠ k → (A *ᵥ x) i ≤ b i} = (HPolytope.ineqs A b).construct := by
    intro k hk
    ext x
    rw [Set.mem_setOf_eq, HPolytope.mem_ineqs_iff]
    refine ⟨fun h => ?_, fun h i _ => h i⟩
    obtain ⟨h0, h1, h3, h4⟩ := hsq x fun i h2 h5 => h i (by rcases hk with rfl | rfl <;> assumption)
    exact hall x h0 h1 h3 h4
  refine ⟨A, b, 5, 2, ![1, 1], by simp, hdrop 5 (Or.inr rfl), ?_, ?_, ?_, hdrop 2 (Or.inl rfl)⟩
  · intro i _
    exact hall ![1, 1] (by simp) (by simp) (by simp) (by simp) i
  -- `(1, 1)` maximizes `x + y` over the square
  · intro x hx
    obtain ⟨h0, h1, -, -⟩ := hsq x fun i _ h5 => hx i h5
    rw [hA, hA]
    simp
    linarith
  · rw [hA]
    simp [b]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
