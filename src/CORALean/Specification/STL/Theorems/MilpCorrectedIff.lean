module

public import CORALean.Specification.STL.Definitions.IsMilpCorrected
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The corrected program (26) finds a factor outside the polytope

`STL.IsMilpCorrected C d α` holds iff `α ∈ [-1, 1]^p` and some row is violated,
`d_k < C_k α`: `α` lies outside `⟨C, d⟩_P`. This is what line 9 of [1, Alg. 3] needs of
the program [1, Eq. (26)], which as printed is infeasible; see `STL.not_milpPrinted_of_two_le`.
The `λ_jk` select a row `k`, the other `α̃_jk` vanish and `α̃ = α̃_jk`.

## Inputs
* `C` – constraint matrix
* `d` – offsets
* `α` – factor vector

## Hypotheses
* none

## Conclusion
* the corrected program holds iff the factor lies in the box and outside the polytope

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {s p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.milpCorrected_iff (C : Matrix (Fin s) (Fin p) ℝ) (d : Fin s → ℝ)
    (α : Fin p → ℝ) : -- --- CONCL ---
    STL.IsMilpCorrected C d α ↔
      (∀ i, -1 ≤ α i ∧ α i ≤ 1) ∧ ∃ k, d k < ∑ i, C k i * α i := by -- --- PROOF ---
  constructor
  · rintro ⟨a, lam, hbin, hstrict, hbox, hα, hsum, hα1⟩
    refine ⟨hα1, ?_⟩
    have hnn : ∀ k, 0 ≤ lam k := fun k => by rcases hbin k with h | h <;> simp [h]
    -- the selected row: some `λ_k = 1`
    obtain ⟨k, hk⟩ : ∃ k, lam k = 1 := by
      by_contra hne
      have hne' := not_exists.mp hne
      simp only [fun k => (hbin k).resolve_right (hne' k), Finset.sum_const_zero] at hsum
      norm_num at hsum
    -- every other `λ_j` is `0`, as they sum to `1`, hence so is `α̃_j`
    have hrest : ∀ j ≠ k, lam j = 0 := by
      have h0 : ∑ j ∈ Finset.univ.erase k, lam j = 0 := by
        have := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ k)
        linarith
      intro j hj
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp h0 j
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    have hzero : ∀ j ≠ k, ∀ i, a j i = 0 := fun j hj i => by
      have := hbox j i
      rw [hrest j hj] at this
      linarith [this.1, this.2]
    have hαk : ∀ i, α i = a k i := fun i => by
      rw [hα i, Finset.sum_eq_single k (fun j _ hj => hzero j hj i) (by simp)]
    refine ⟨k, ?_⟩
    simpa [hk, hαk] using hstrict k hk
  · rintro ⟨hbox, k, hk⟩
    -- select row `k`: `λ` its indicator and `α̃_jk = α`
    refine ⟨fun j i => if j = k then α i else 0, fun j => if j = k then 1 else 0, ?_, ?_, ?_, ?_,
      ?_, hbox⟩
    · intro j; by_cases h : j = k <;> simp [h]
    · intro j hj
      by_cases h : j = k
      · subst h; simpa using hk
      · simp [h] at hj
    · intro j i; by_cases h : j = k
      · subst h; simpa using hbox i
      · simp [h]
    · intro i; simp
    · simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
