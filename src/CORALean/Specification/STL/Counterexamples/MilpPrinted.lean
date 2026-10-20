module

public import CORALean.Specification.STL.Theorems.MilpPrintedInfeasible
public import CORALean.Specification.STL.Theorems.MilpCorrectedIff

@[expose] public section

/-!
# The program (26) as printed is infeasible where a falsifying factor exists

For the polytope `{x | x ≤ 1/2 ∧ -x ≤ 1/2}` of `p = 1`, `s = 2`, a conjunction of two halfspaces,
the factor `α̃ = 1 ∈ [-1, 1]` lies outside it: `1 > 1/2`. The program [1, Eq. (26)] as printed
has no solution there, [1, Alg. 3] would not find the falsifying factor, while the corrected
program is solved by it. By `STL.not_milpPrinted_of_two_le` and `STL.milpCorrected_iff`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed program is infeasible where the corrected one is feasible

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.milpPrinted_counterexample :
    ∃ (C : Matrix (Fin 2) (Fin 1) ℝ) (d : Fin 2 → ℝ) (α : Fin 1 → ℝ),
      STL.milpCorrected C d α ∧ ¬ STL.milpPrinted C d α := by -- --- PROOF ---
  refine ⟨fun k _ => if k = 0 then 1 else -1, fun _ => (1 : ℝ) / 2, fun _ => 1, ?_,
    STL.not_milpPrinted_of_two_le _ _ _ (le_refl 2)⟩
  rw [STL.milpCorrected_iff]
  refine ⟨fun i => by norm_num, 0, ?_⟩
  simp
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
