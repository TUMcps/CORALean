module

public import CORALean.HybridDynamics.Parallel.Theorems.MergeFlowsLinearSysFlow
public import CORALean.HybridDynamics.Parallel.Definitions.FlowLaw
public import CORALean.HybridDynamics.Parallel.Definitions.FeedthroughFree
public import CORALean.HybridDynamics.Parallel.Operations.MergeInputSets
public import CORALean.HybridDynamics.Parallel.Operations.MergeDistSets

@[expose] public section

/-!
# The product's flow has the flow law

At `ℝ` and under CORA's own check `FeedthroughFree`, `mergeFlowsLinearSys` with `mergeInputSets`
and `mergeDistSets` has `FlowLaw`: for states, bound inputs, admitted global inputs `g` and
disturbances `w` of the components, the product's input is `g` with the global inputs nothing
reads set to `0` (in `mergeInputSets` by `Lifting.mem_input`), its disturbance the stack of `w`
(in `mergeDistSets` by `Lifting.mem_dist`), and `mergeFlowsLinearSys_flow` is the coordinate
identity. So every run theorem stated for `FlowLaw` holds of `product`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.mergeFlowsLinearSys_flowLaw
    {P : ParallelHybridAutomaton S G k L ℝ n m} (hfeed : P.FeedthroughFree)
    (lift : ParallelHybridAutomaton.Lifting S G n m) :
    P.FlowLaw (fun ℓ => mergeFlowsLinearSys (P.sys ℓ) (P.bindsAt ℓ)) (P.mergeInputSets lift)
      (P.mergeDistSets lift) := by -- --- PROOF ---
  classical
  intro ℓ x u w g hu hin hw
  -- the product's input: `g`, zero at the global inputs no input reads
  set g' : Vec ℝ m := fun a => if ∃ i j, P.bindsAt ℓ i j = .global a then g a else 0 with hg'
  have hfed : ∀ i j a, P.bindsAt ℓ i j = .global a → g' a = g a := fun i j a h => by
    simp only [hg']
    rw [if_pos ⟨i, j, h⟩]
  refine ⟨g', stack w, lift.mem_input _ _ g' (fun i => ?_) (fun a ha => ?_),
    lift.mem_dist _ w hw, fun i a => ?_⟩
  · -- the components' points agree with `g`, so with `g'`
    obtain ⟨v, hv, hva⟩ := hin i
    exact ⟨v, hv, fun j a h => (hva j a h).trans (hfed i j a h).symm⟩
  · -- nothing reads `a`
    simp only [hg']
    rw [if_neg fun ⟨i, j, h⟩ => ha i j h]
  · -- the merged equation, its bound inputs those of the components, with `g'` for `g`
    have := mergeFlowsLinearSys_flow (P.sys ℓ) (P.bindsAt ℓ)
      (fun i j c s h j' c' s' h' => hfeed ℓ i j c s h j' c' s' h') x g' w u (fun i j => by
        rw [hu i j]
        unfold ParallelHybridAutomaton.boundInput
        cases h : P.bindsAt ℓ i j with
        | global a => exact (hfed i j a h).symm
        | output c s => rfl) i a
    simpa only [Pi.add_apply, Scalar.toRealMat_real, Scalar.toRealVec_real] using this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
