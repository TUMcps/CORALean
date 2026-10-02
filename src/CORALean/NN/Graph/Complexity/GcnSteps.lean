import CORALean.NN.Graph.Complexity.ConvUncertain
import CORALean.NN.Graph.Operations.GcnSteps
import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# `GNN.gcnSteps`'s count over a chain of steps

The recursion [1, Thm. 1] unrolls, as a bound: one step takes `h` to
`(P.h + 1)(h + 1)`, so `h + 1` is multiplied by `P.h + 1` and then grows by one,
and `P.h + 2` absorbs both — `L` steps leave at most `(P.h + 2)^L (H.h + 1)`.

A bound and not a count, since the exact closed form carries the geometric sum
the `+1` per step contributes, and the factor `(P.h + 2)^L` is what the
asymptotics in `GcnStepsBigO.lean` read. Stated on `h + 1` rather than on `h`
because that is the quantity the recursion is linear in.

`W` and `H` stay universally quantified inside the induction: a step hands the
next one a different set, so the hypothesis has to hold for all of them.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `L` message-passing steps at one uncertain graph multiply the generator
count by at most `P.h + 2` each. -/
theorem GNN.gcnSteps_h_le (P : PolyZonotope (Mat ℝ N N)) (L : ℕ) :
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
