module

public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsLinearSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.HybridDynamics.Parallel.Definitions.IsSelfBindFree
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `IsSelfBindFree` cannot be dropped from `mergeFlows`

One state-bound component, `ẋ = x + u`, `y = x`, its input bound to its own output. CORA's merge
`mergeFlowsLinearSys` has `A + B C`, the one entry `2`: the flow is `ẋ = 2 x`. `mergeFlows` builds
the entry `1` (the `1` of `B C` replaces `A_ij`), so its flow law fails here: the hypothesis is
needed, not an artefact of the proof (#40).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the merge without arithmetic differs from the full merge
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The state `1`. -/
@[step_of ParallelHybridAutomaton.mergeFlows_selfBind_counterexample]
def SBC.step_one : Vec ℝ 1 := fun _ => 1

/-- The component: `ẋ = x + u`, `y = x`, in `[0, 1]`, with zero input and disturbance sets and
no transitions. -/
@[step_of ParallelHybridAutomaton.mergeFlows_selfBind_counterexample]
def SBC.step_comp : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { inv := HPolytope.slab (1 : Mat ℝ 1 1) ![0] ![1]
      dynamics := LinearSys.canonical !![1]
      U := ⟨![0], ![0]⟩
      W := ⟨![0], ![0]⟩
      trans := [] }

/-- Its one input is its own output. -/
@[step_of ParallelHybridAutomaton.mergeFlows_selfBind_counterexample]
def SBC.step_parallel : ParallelHybridAutomaton ℐ𝒱 ℋ𝒫 1 (fun _ => Unit) ℝ (fun _ => 1) 0 where
  comp := fun _ => SBC.step_comp
  p := fun _ => 1
  q := fun _ => 1
  binds := fun _ _ => .output 0 0
  inputs_eq := fun _ _ => rfl
  outputs_eq := fun _ _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mergeFlows` reads `1` where CORA's merge, and the flow, is `1 + 1`: not `IsSelfBindFree`. -/
theorem ParallelHybridAutomaton.mergeFlows_selfBind_counterexample : -- --- CONCL ---
    ¬ SBC.step_parallel.IsSelfBindFree ∧
    (toRealMat (SBC.step_parallel.mergeFlows fun _ => ()).A *ᵥ stack fun _ => SBC.step_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 1 ∧
    ((ParallelHybridAutomaton.mergeFlowsLinearSys (SBC.step_parallel.sys fun _ => ())
        (SBC.step_parallel.bindsAt fun _ => ())).A *ᵥ stack fun _ => SBC.step_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 2 := by -- --- PROOF ---
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := h (fun _ => ()) 0 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩ 0 0 rfl rfl rfl
    simp [SBC.step_parallel, SBC.step_comp] at this
    exact one_ne_zero this
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlows, ParallelHybridAutomaton.bindsAt, SBC.step_parallel,
      SBC.step_comp, SBC.step_one, stack]
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlowsLinearSys, ParallelHybridAutomaton.bindsAt,
      SBC.step_parallel, SBC.step_comp, SBC.step_one, stack]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
