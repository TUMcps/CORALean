module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `[1, Sec. 4.1 (interval hull)]`'s interval-hull heuristic at an empty polytope

`{x ≤ 0, -x ≤ -1}` is empty, so its interval hull is empty and every halfspace contains it
strictly. Removing `x ≤ 0` leaves `{x ≥ 1}`, which is not empty: the heuristic needs a nonempty
polytope, which `ineqs_eq_of_strict` assumes.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `[1, Sec. 4.1 (interval hull)]`'s interval-hull heuristic at an empty polytope

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

theorem HPolytope.ineqs_eq_of_strict_counterexample : -- --- CONCL ---
    ∃ (A : Mat ℝ 2 1) (b : Vec ℝ 2) (J : Finset (Fin 2)) (T : Set (Vec ℝ 1)),
      (HPolytope.ineqs A b).construct ⊆ T ∧ (∀ x ∈ T, ∀ j ∈ J, (A *ᵥ x) j < b j) ∧
      {x | ∀ i, i ∉ J → (A *ᵥ x) i ≤ b i} ≠ (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  refine ⟨!![1; -1], ![0, -1], {0}, ∅, fun x hx => ?_, fun x hx => hx.elim, fun h => ?_⟩
  -- the polytope is empty: `x ≤ 0` and `x ≥ 1`
  · have h0 := HPolytope.mem_ineqs_iff.mp hx 0
    have h1 := HPolytope.mem_ineqs_iff.mp hx 1
    simp [mulVec, dotProduct] at h0 h1
    linarith
  -- yet `1` keeps the remaining row
  · have hmem : (![1] : Vec ℝ 1) ∈ {x : Vec ℝ 1 | ∀ i, i ∉ ({0} : Finset (Fin 2)) →
        ((!![1; -1] : Mat ℝ 2 1) *ᵥ x) i ≤ (![0, -1] : Vec ℝ 2) i} := by
      intro i hi
      fin_cases i
      · exact absurd (Finset.mem_singleton_self _) hi
      · simp [mulVec, dotProduct]
    rw [h] at hmem
    have := HPolytope.mem_ineqs_iff.mp hmem 0
    simp [mulVec, dotProduct] at this
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
