import CORALean.HybridDynamics.Parallel.API
import CORALean.Examples.ParallelTwoComponents

/-!
# Two components that must jump together

`ParallelTwoComponents`' two one-dimensional components, each now with one transition labeled
`()`, the same label: neither may be taken alone. `mergeTransitionSets` lifts the two
transitions one by one and so has two product transitions, which is what a labeled automaton
must not have; `mergeTransitionSetsSync` has exactly one, the synchronized transition of both.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet

/-- Component `1`: integrates its global input, and has one transition, back to itself. -/
def PSY.integrator : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { PTC.integrator.loc () with
      trans := [⟨HPolytope.ineqs !![-1] ![1], !![1], 0, ()⟩] }

/-- The parallel automaton: `PTC.decay` and `PSY.integrator`, bound as in `PTC`. -/
def PSY.parallel :
    ParallelHybridAutomaton ℐ𝒱 ℋ𝒫 2 (fun _ => Unit) ℝ (fun _ => 1) 1 where
  comp := ![PTC.decay, PSY.integrator]
  binds := PTC.binds

/-- Every transition carries the label `()`, which both components share. -/
def PSY.labels : ParallelHybridAutomaton.SyncLabels ℋ𝒫 (fun _ : Fin 2 => Unit) ℝ (fun _ => 1)
    Unit where
  label _ _ := some ()
  parts _ _ := true
  labels := [()]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Without labels the two transitions are lifted alone: two product transitions. -/
theorem PSY.unsynchronized_length (ℓ : ∀ _ : Fin 2, Unit) :
    (PSY.parallel.mergeTransitionSets (ParallelHybridAutomaton.boxLifting PTC.binds) ℓ).length =
      2 := by
  simp [ParallelHybridAutomaton.mergeTransitionSets, PSY.parallel,
    PTC.decay, PSY.integrator, PTC.integrator, List.finRange, List.ofFn_succ]

/-- With the label they are lifted together: one product transition. -/
theorem PSY.synchronized_length (ℓ : ∀ _ : Fin 2, Unit) :
    (PSY.parallel.mergeTransitionSetsSync (ParallelHybridAutomaton.boxSyncLifting PTC.binds)
      PSY.labels ℓ).length = 1 := by
  simp [ParallelHybridAutomaton.mergeTransitionSetsSync, PSY.parallel, PSY.labels,
    ParallelHybridAutomaton.SyncLabels.pick, PTC.decay, PSY.integrator, PTC.integrator,
    List.finRange, List.ofFn_succ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
