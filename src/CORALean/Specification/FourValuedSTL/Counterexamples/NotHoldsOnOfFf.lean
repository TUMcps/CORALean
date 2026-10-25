module

public import CORALean.Specification.FourValuedSTL.Definitions.Basic
public import CORALean.Specification.FourValuedSTL.Operations.FourValuedSat
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.Basic
public import CORALean.Specification.FourValuedSignal.Theorems.AtNot

@[expose] public section

/-!
# A system without executions satisfies every formula

The last sentence of [1, Cor. 1], "`⟦φ⟧_R̃(0) = ⊥` implies `H ⊭ φ`", fails for a system with no
execution: `⟦¬true⟧_R̃(0) = ¬⊤ = ⊥` for every partial reachable set `R̃`, while `H ⊨ ¬true` holds
vacuously for `E = ∅` ([1, Sec. 2.5]); `FourValuedSTL.verdict_system` proves it for `E` nonempty.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a formula with verdict false holds on the system without executions

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSTL.not_holdsOn_of_ff_counterexample : -- --- CONCL ---
    ∃ r, (FourValuedSTL.Formula.not .tt : FourValuedSTL.Formula Unit).fourValuedSat
        (fun _ => FourValuedSignal.uniformSignal .ii) = some r ∧ r.IsValid ∧
      r.at 0 = FourValued.ff ∧
      (FourValuedSTL.Formula.not .tt : FourValuedSTL.Formula Unit).HoldsOn ∅ := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := FourValuedSignal.uniformSignal_spec FourValued.tt
  refine ⟨(FourValuedSignal.uniformSignal FourValued.tt).not, rfl,
    FourValuedSignal.not_isValid _ hv, ?_, fun ξ hξ => absurd hξ (Set.notMem_empty ξ)⟩
  rw [FourValuedSignal.at_not _ hv, h 0 le_rfl]
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
