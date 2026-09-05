import CORALean.NN.RefinableNetwork

/-!
# What it takes for refinement to converge

Convergence is stated by a Minkowski inflation and no metric on sets: the
propagated set is inside the exact image widened by the closed `ε`-ball. The
other direction is `propagateAt_outer`, so the two together say the enclosure is
squeezed onto the image — with `Pointwise` addition doing all the work and no
Hausdorff distance to define, to relate to `construct`, or to prove complete.

A layer is `Convergent` when every input set admits a level meeting any `ε`. The
network asks for that of each layer *and* for a Lipschitz bound on the layers
after it: an earlier layer's residual is amplified by everything downstream, so
without one a vanishing residual buys nothing at the output. The bound is a
hypothesis rather than a weakened claim, and it is one every standard layer
meets — a linear layer by its matrix, an activation by its own slope.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}

/-- Some level brings the enclosure inside any inflation of the exact image. -/
def RefinableLayer.Convergent (L : RefinableLayer S n m) : Prop :=
  ∀ (s : S n) (ε : ℝ), 0 < ε →
    ∃ o : ℕ, construct (L.propagate o s) ⊆ L.eval '' construct s + Metric.closedBall 0 ε

/-- Every layer convergent, and every tail Lipschitz so that a residual left
early is still small at the output. -/
def RefinableNetwork.Convergent : ∀ {n m : ℕ}, RefinableNetwork S n m → Prop
  | _, _, .nil => True
  | _, _, .cons L rest =>
      L.Convergent ∧ (∃ K : NNReal, LipschitzWith K rest.eval) ∧ rest.Convergent

end CORALean.Real
