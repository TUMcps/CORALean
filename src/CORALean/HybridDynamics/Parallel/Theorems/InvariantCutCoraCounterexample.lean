import CORALean.HybridDynamics.Parallel.Operations.InvariantCutCora
import CORALean.HybridDynamics.Parallel.Operations.InvariantCutDocumented

/-!
# CORA's invariant cut is not the one it documents

A polytope guard whose label is not merged (an unlabeled transition's included): CORA cuts the
invariant by its complement, the documented condition does not. Read from
`@parallelHybridAutomaton/mergeInvariants.m`, not run (#40, `FINDINGS.md`).
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.invariantCutCora_counterexample :
    ParallelHybridAutomaton.invariantCutCora true false false = true ∧
      ParallelHybridAutomaton.invariantCutDocumented true false false = false := by
  exact ⟨rfl, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
