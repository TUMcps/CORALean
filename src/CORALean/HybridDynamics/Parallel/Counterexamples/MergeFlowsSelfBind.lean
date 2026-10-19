module

public import CORALean.HybridDynamics.Parallel.Operations.Basic
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlows
public import CORALean.HybridDynamics.Parallel.Operations.MergeFlowsLinearSys
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `SelfBindFree` cannot be dropped from `mergeFlows`

One state-bound component, `ẋ = x + u`, `y = x`, its input bound to its own output. CORA's merge
`mergeFlowsLinearSys` has `A + B C`, the one entry `2`: the flow is `ẋ = 2 x`. `mergeFlows` builds
the entry `1` (the `1` of `B C` replaces `A_ij`), so its flow law fails here: the hypothesis is
needed, not an artefact of the proof (#40).
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state `1`. -/
def SBC.aux_one : Vec ℝ 1 := fun _ => 1

/-- The component: `ẋ = x + u`, `y = x`, in `[0, 1]`, with zero input and disturbance sets and
no transitions. -/
def SBC.aux_comp : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { inv := HPolytope.slab (1 : Mat ℝ 1 1) ![0] ![1]
      dynamics := LinearSys.canonical !![1]
      U := ⟨![0], ![0]⟩
      W := ⟨![0], ![0]⟩
      trans := [] }

/-- Its one input is its own output. -/
def SBC.aux_parallel : ParallelHybridAutomaton ℐ𝒱 ℋ𝒫 1 (fun _ => Unit) ℝ (fun _ => 1) 0 where
  comp := fun _ => SBC.aux_comp
  p := fun _ => 1
  q := fun _ => 1
  binds := fun _ _ => .output 0 0
  inputs_eq := fun _ _ => rfl
  outputs_eq := fun _ _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mergeFlows` reads `1` where CORA's merge, and the flow, is `1 + 1`: not `SelfBindFree`. -/
theorem ParallelHybridAutomaton.mergeFlows_selfBind_counterexample : -- --- CONCL ---
    ¬ SBC.aux_parallel.SelfBindFree ∧
    (toRealMat (SBC.aux_parallel.mergeFlows fun _ => ()).A *ᵥ stack fun _ => SBC.aux_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 1 ∧
    ((ParallelHybridAutomaton.mergeFlowsLinearSys (SBC.aux_parallel.sys fun _ => ())
        (SBC.aux_parallel.bindsAt fun _ => ())).A *ᵥ stack fun _ => SBC.aux_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 2 := by -- --- PROOF ---
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := h (fun _ => ()) 0 ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩ 0 0 rfl rfl rfl
    simp [SBC.aux_parallel, SBC.aux_comp] at this
    exact one_ne_zero this
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlows, ParallelHybridAutomaton.bindsAt, SBC.aux_parallel,
      SBC.aux_comp, SBC.aux_one, stack]
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlowsLinearSys, ParallelHybridAutomaton.bindsAt,
      SBC.aux_parallel, SBC.aux_comp, SBC.aux_one, stack]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
