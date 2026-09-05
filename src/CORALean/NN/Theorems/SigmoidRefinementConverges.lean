import CORALean.NN.Layers.SigmoidPolyRefine
import CORALean.NN.Theorems.PropagateAtInflate

/-!
# The network statement, at a network that exists

`PropagateAtInflate` runs on a hypothesis — every layer convergent, every tail
Lipschitz — and a hypothesis is worth only what satisfies it. This discharges it
at a sigmoid layer, so the schedule it produces is one an implementation could
be asked for.

The tail is empty and its `eval` is the identity, which is where the Lipschitz
constant comes from. That is the easy case of the hypothesis, and deliberately
so: the point being made is that the *layer* half is met at a real activation,
`Layer.activationPolySigmoid_convergent` being the part with content.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise ContSet

theorem sigmoidRefinableNetwork_convergent (n : ℕ) : (sigmoidRefinableNetwork n).Convergent :=
  ⟨Layer.activationPolySigmoid_convergent n, ⟨1, LipschitzWith.id⟩, trivial⟩

/-- The loop converges there: some schedule is inside any inflation of the exact
output set, which with `propagateAt_outer` squeezes the enclosure onto it. -/
theorem exists_schedule_sigmoid_subset {n : ℕ} (X : PolyZonotope (Vec ℝ n)) {ε : ℝ}
    (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((sigmoidRefinableNetwork n).propagateAt sch X)
        ⊆ (sigmoidRefinableNetwork n).outputSet X + Metric.closedBall 0 ε :=
  (sigmoidRefinableNetwork n).exists_schedule_propagateAt_subset
    (sigmoidRefinableNetwork_convergent n) X ε hε

end CORALean.Real
