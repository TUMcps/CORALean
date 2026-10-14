module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.Global.DropIdx
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An H-representation of the empty set need not be minimal

[1, Sec. 3 (minimal representation)]: "it holds in general that a) empty sets are bounded,
degenerate, and in minimal representation", minimal meaning "represented by a minimal amount of
halfspaces". That is a property of a representation, not of a set, and not every H-representation of
`∅` has it: `x ≤ -1`, `-x ≤ -1`, `x ≤ 5` describes `∅`, and so do the first two rows alone, so the
third is redundant in the sense of [1, Eq. 1]. What does hold is `HPolytope.emptySet_rows_minimal`:
the one-row representation CORA uses has the fewest rows any H-representation of `∅` can have.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (minimal representation)]: an H-representation of `∅` with a redundant row. -/
theorem HPolytope.empty_redundant_counterexample :
    ∃ (A : Mat ℝ 3 1) (b : Vec ℝ 3) (j : Fin 3),
      (HPolytope.ineqs A b).construct = ∅ ∧
      (HPolytope.ineqs (A.submatrix (dropIdx j) id) fun i => b (dropIdx j i)).construct
        = (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  refine ⟨![![1], ![-1], ![1]], ![-1, -1, 5], 2, ?_, ?_⟩
  · -- `x ≤ -1` and `-x ≤ -1` already contradict
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have h := HPolytope.mem_ineqs_iff.mp hx
    have h0 := h 0
    have h1 := h 1
    simp [mulVec, dotProduct] at h0 h1
    linarith
  · -- the same two rows survive the drop, so the smaller system is empty too
    ext x
    rw [HPolytope.mem_ineqs_iff, HPolytope.mem_ineqs_iff]
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      have hd0 : dropIdx (2 : Fin 3) 0 = 0 := rfl
      have hd1 : dropIdx (2 : Fin 3) 1 = 1 := rfl
      simp [mulVec, dotProduct, hd0, hd1] at h0 h1
      linarith
    · intro h i
      have h0 := h 0
      have h1 := h 1
      simp [mulVec, dotProduct] at h0 h1
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
