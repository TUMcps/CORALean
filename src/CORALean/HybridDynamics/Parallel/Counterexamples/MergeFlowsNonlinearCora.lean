module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `mergeFlowsNonlinearCora`: the input of a component fed by another's output, as CORA merges it

`@parallelHybridAutomaton/mergeFlows.m`, `aux_mergeFlowsNonlinearSys` (l. 270-306), resolves the
input `j` of a component that is bound to output `k` of a feeding component by `outTemp =
feedingFlow.out_mFile(xTemp, uTemp)(k)`. If `outTemp` does not depend on the feeding component's
own inputs (`outTemp - subs(outTemp, uTemp, 0) == 0`, l. 280) then `u_(j) = outTemp` (l. 282).
Otherwise (l. 284-304) each `uTemp(uu)` that occurs is replaced in `outTemp` by the global input
it is bound to, but `outTemp` is never assigned to `u_(j)`, which was initialised to `0`
(`sym(zeros(..))`, l. 259). The receiving component sees the input `0`. The linear merge
(`aux_mergeFlowsLinearSys`) carries the same case through `D`.

Modelled at the smallest level: a feeding output `y(x, v)` of one state coordinate `x` and one
input `v`, bound to the global input `g`. Read from the source, not run.

# CORA's nonlinear `mergeFlows` drops a global input that reaches a bound output

Component A has the output `y = x_A + u_A` with `u_A` the global input, component B has
`ẋ_B = u_B` with `u_B` bound to `y`. The merged flow should have `ẋ_B = x_A + g`; CORA's gives
`ẋ_B = 0`. Read from `mergeFlows.m` l. 280-306, not run
(`references/coverage/hybridDynamics/parallelHybridAutomaton.md`, row `mergeFlows`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- The input that CORA's code gives the receiving component: `outTemp` if the output does not
depend on the feeding component's input (`indep`, the symbolic test of l. 280), else the initial
`0` of `u_(j)`. The intended input is `y x g`, the output at the global input `g`. -/
def ParallelHybridAutomaton.feedInputCora {α : Type} [Zero α] (y : α → α → α) (_g x : α)
    (indep : Prop) [Decidable indep] : α :=
  if indep then y x 0 else 0


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- For `y = x + v` the output depends on its input, so CORA's input of B is `0` at every state and
global input, where the intended `y x g = x + g` is `2` at `x = g = 1`. -/
theorem ParallelHybridAutomaton.feedInputCora_counterexample :
    (∀ g x : ℝ, ParallelHybridAutomaton.feedInputCora (fun x v => x + v) g x
      (∀ x' v : ℝ, x' + v = x' + 0) = 0) ∧
      ParallelHybridAutomaton.feedInputCora (fun x v => x + v) 1 1 (∀ x' v : ℝ, x' + v = x' + 0) ≠
        (fun x v : ℝ => x + v) 1 1 := by -- --- PROOF ---
  -- the output depends on its input: v = 1 at x' = 0
  have hdep : ¬ ∀ x' v : ℝ, x' + v = x' + 0 := fun h => by
    have := h 0 1; norm_num at this
  have h0 : ∀ g x : ℝ, ParallelHybridAutomaton.feedInputCora (fun x v => x + v) g x
      (∀ x' v : ℝ, x' + v = x' + 0) = 0 := by
    intro g x
    simp only [ParallelHybridAutomaton.feedInputCora, if_neg hdep]
  refine ⟨h0, ?_⟩
  rw [h0]
  norm_num

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
