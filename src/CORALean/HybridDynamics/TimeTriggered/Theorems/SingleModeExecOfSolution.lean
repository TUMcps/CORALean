module

public import CORALean.HybridDynamics.TimeTriggered.Operations.SingleMode
public import CORALean.HybridDynamics.TimeTriggered.Theorems.FlowsOfHasDerivAt

@[expose] public section

/-!
# A solution from an initial state is an execution of the single-mode automaton

The converse of `singleMode_exists_solution_of_exec`: a solution of `ẋ = f(x)` on `[0, s]` that
starts in `I` is one continuous successor of an initial state of `H_single`, of duration `s`, in
the sense of [1, Def. 6].

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of `ẋ = f(x)` on `[0, s]` from `I` ends an execution of duration `s`. -/
theorem DiffInclAutomaton.singleMode_exec_of_solution {I : Set X} {f : X → X} {s : ℝ}
    (hs : 0 ≤ s) {z : ℝ → X} (hz0 : z 0 ∈ I) (hz : ∀ u ∈ Icc 0 s, HasDerivAt z (f (z u)) u) :
    (DiffInclAutomaton.singleMode I f).Exec s () (z s) := by -- --- PROOF ---
  have e0 : (DiffInclAutomaton.singleMode I f).Exec 0 () (z 0) :=
    DiffInclAutomaton.Exec.init hz0
  rcases hs.eq_or_lt with rfl | hpos
  · exact e0
  · have := e0.flow (DiffInclAutomaton.flows_of_hasDerivAt (v := fun u => f (z u))
      (H := DiffInclAutomaton.singleMode I f) (m := ()) hpos hz
      (fun u _ => by simp [DiffInclAutomaton.singleMode]) (fun u _ => by
        simp [DiffInclAutomaton.singleMode]))
    simpa using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
