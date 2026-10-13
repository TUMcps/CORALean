module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsAddMulVec
public import CORALean.HybridDynamics.Parallel.Definitions.SelfBindFree
public import CORALean.ContSet.HPolytope.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Slab
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# `SelfBindFree` cannot be dropped from `mergeFlows`

One component, `ẋ = x + u`, its input bound to its own state. The flow is `ẋ = 2 x`, and
`mergeFlowsAdd` has the one entry `2` as its matrix; `mergeFlows` builds the entry `1` (the `1`
replaces `A_ij`), so `mergeFlows_mulVec` fails here: the hypothesis is needed, not an artefact of
the proof (#40).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The state `1`. -/
def SBC.aux_one : Vec ℝ 1 := fun _ => 1

/-- The component: `ẋ = x + u`, in `[0, 1]`, with a zero input set and no transitions. -/
def SBC.aux_comp : HybridAutomaton ℐ𝒱 ℋ𝒫 Unit ℝ 1 where
  loc _ :=
    { inv := HPolytope.slab (1 : Mat ℝ 1 1) ![0] ![1]
      dynamics := ⟨!![1]⟩
      U := ⟨![0], ![0]⟩
      trans := [] }

/-- Its one input is its own state. -/
def SBC.aux_parallel : ParallelHybridAutomaton ℐ𝒱 ℋ𝒫 1 (fun _ => Unit) ℝ (fun _ => 1) 0 where
  comp := fun _ => SBC.aux_comp
  binds := fun _ _ => .state 0 0


-- =======================================  MAIN THEOREM  ======================================= --

/-- `mergeFlows` reads `1` where the flow is `1 + 1`: not `SelfBindFree`, and the flow law fails. -/
theorem ParallelHybridAutomaton.mergeFlows_selfBind_counterexample :
    ¬ SBC.aux_parallel.SelfBindFree ∧
    (toRealMat (SBC.aux_parallel.mergeFlows fun _ => ()).A *ᵥ stack fun _ => SBC.aux_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 1 ∧
    (toRealMat (SBC.aux_parallel.mergeFlowsAdd fun _ => ()).A *ᵥ stack fun _ => SBC.aux_one)
        (finSigmaFinEquiv ⟨0, 0⟩) = 2 ∧
    (toRealMat ((SBC.aux_parallel.comp 0).loc ()).dynamics.A *ᵥ SBC.aux_one) 0 +
      SBC.aux_one 0 = 2 := by -- --- PROOF ---
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · have := h (fun _ => ()) 0 0 0 rfl
    simp [SBC.aux_parallel, SBC.aux_comp] at this
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlows, SBC.aux_parallel, SBC.aux_comp, SBC.aux_one, stack]
  · rw [Matrix.mulVec, dotProduct, ← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma]
    simp [ParallelHybridAutomaton.mergeFlowsAdd, SBC.aux_parallel, SBC.aux_comp, SBC.aux_one, stack]
    norm_num
  · simp [SBC.aux_parallel, SBC.aux_comp, SBC.aux_one, Matrix.mulVec, dotProduct]
    norm_num

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
