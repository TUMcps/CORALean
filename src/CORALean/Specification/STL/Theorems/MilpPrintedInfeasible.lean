module

public import CORALean.Specification.STL.Definitions.MilpPrinted
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The program (26) as printed has no solution for two rows or more

With `s ≥ 2` rows, the binaries `λ_jk` sum to `1`, so one is `0`, and its `α̃_jk` is `0` by
`|α̃_jk| ≤ λ_jk`: the printed `C_j(·,k) α̃_jk > λ_jk d_j(k)` reads `0 > 0`. So [1, Eq. (26)] is
infeasible, and [1, Alg. 3] never returns unsafe, for any polytope of two or more halfspaces, which
a conjunction of two predicates gives. `STL.milpCorrected_iff` is the repair.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {s p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.not_milpPrinted_of_two_le (C : Matrix (Fin s) (Fin p) ℝ) (d : Fin s → ℝ)
    (α : Fin p → ℝ) (hs : 2 ≤ s) : ¬ STL.milpPrinted C d α := by -- --- PROOF ---
  rintro ⟨a, lam, hbin, hstrict, hbox, -, hsum, -⟩
  -- some `λ_jk` is `0`: all `1` would sum to `s ≥ 2`
  have hex : ∃ k, lam k = 0 := by
    by_contra hne
    have hne' := not_exists.mp hne
    have h1 : ∀ k, lam k = 1 := fun k => (hbin k).resolve_left (hne' k)
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at hsum
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  obtain ⟨k, hk⟩ := hex
  -- its `α̃_jk` is `0`, and the constraint reads `0 > 0`
  have ha : ∀ i, a k i = 0 := fun i => by
    have := hbox k i
    rw [hk] at this
    linarith [this.1, this.2]
  have := hstrict k
  simp only [ha, hk, mul_zero, Finset.sum_const_zero, zero_mul] at this
  exact lt_irrefl _ this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
