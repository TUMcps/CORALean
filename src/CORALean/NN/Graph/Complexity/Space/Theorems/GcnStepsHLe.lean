module

public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnSharedH
public import CORALean.NN.Graph.Operations.GcnSteps
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureP
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHIsBigO

@[expose] public section

/-!
# `GNN.gcnSteps`'s count over a chain of steps

The recursion [1, Thm. 1] unrolls, as a bound: `L` steps leave at most `(P.h + 2)^L (H.h + 1)`
generators. A bound and not a count, since the exact closed form carries the geometric sum the `+1`
per step contributes; stated on `h + 1` because that is what the recursion is linear in.

`gcnSteps_h_isBigO` is [1, Thm. 1]'s `h_e^(3κ')` term for the graph half of the pipeline:
`O(m^(3L))` generators in the number `m` of uncertain edges. The other two terms, `|N| c_max` and
`(κ - 2κ') n_max`, are [1, Prop. 1]'s one generator per activation output neuron.

## Inputs
* `P` – polynomial zonotope of the graph
* `L` – number of steps

## Hypotheses
* none

## Conclusion
* after L steps the generator count is at most a power of P.h + 2 times the input's

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L` message-passing steps at one uncertain graph multiply the generator
count by at most `P.h + 2` each. -/
theorem GNN.gcnSteps_h_le (P : PolyZonotope (Mat ℝ N N)) (L : ℕ) : -- --- CONCL ---
    ∀ (W : Fin L → Mat ℝ F F) (H : PolyZonotope (Mat ℝ N F)) (hp : P.p = H.p),
      (GNN.gcnSteps P L W H hp).h + 1 ≤ (P.h + 2) ^ L * (H.h + 1) := by -- --- PROOF ---
  induction L with
  | zero =>
    -- no step at all: the chain is its own input
    intro _ H _
    show H.h + 1 ≤ (P.h + 2) ^ 0 * (H.h + 1)
    simp
  | succ L ih =>
    intro W H hp
    -- the step's own count, with the `+1` folded into the base of the power
    have hstep : (GNN.gcnShared (W 0) P H hp).h + 1 ≤ (P.h + 2) * (H.h + 1) := by
      rw [GNN.gcnShared_h]
      nlinarith
    have hih := ih (fun i => W i.succ) (GNN.gcnShared (W 0) P H hp) rfl
    calc (GNN.gcnSteps P (L + 1) W H hp).h + 1
        ≤ (P.h + 2) ^ L * ((GNN.gcnShared (W 0) P H hp).h + 1) := hih
      _ ≤ (P.h + 2) ^ L * ((P.h + 2) * (H.h + 1)) := Nat.mul_le_mul (le_refl _) hstep
      _ = (P.h + 2) ^ (L + 1) * (H.h + 1) := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
