import CORALean.ContDynamics.LinearSysDT.Operations
import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT
import CORALean.NN.Operations.Propagate

/-!
# A network in the loop: reachability

The alternation and nothing else: propagate the current enclosure through the
controller to enclose the inputs it can produce there, and hand that to the
plant as one step's input set. Both halves are already written, so this file
computes nothing new — `LinearSysDT.reach ... 1` is the step and
`NeuralNetwork.propagate` is the input set it takes.

A `def`, for the reason `relinReach` gives: what reachability produces is data
the caller hands to `Specification`, not a set a proof asserts to exist.

The precision is lost in one place, and it is worth naming. `propagate` runs on
the same set the step is taken from, and `plus` then combines the two — so every
state in the enclosure is paired with every input in it, not with the input the
controller produces at that state. The closed loop is deterministic and this
enclosure is not, and no order bound recovers the difference.

`o` is uniform across steps, as in `LinearSysDT.reach`, so the recursion is on
the step index alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

/-- The reachable set of the closed loop after `k` steps, from `R₀`, held at
maximum order `o`. -/
def NeurNetContrSysDT.reach (sys : NeurNetContrSysDT 𝕋 S n) (o : ℕ) (R₀ : S n) : ℕ → S n
  | 0 => R₀
  | k + 1 => sys.plant.reach o (sys.reach o R₀ k)
      (sys.contr.propagate (sys.reach o R₀ k)) 1

end CORALean.Real
