import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the output set holds of the output

What an output equation is added for: until there is one, a requirement can only
be written about the state, and a system whose safety is a property of what it
*emits* has no way to say so. This is `outputSet_outer` handed to
`Specification.holds_of_outer`, the same step `LinearSysDT.holds_of_reach` and
`NeuralNetwork.holds_of_propagate` take.

The specification lives at the output dimension `r`, not at `n`, which is the
whole point: `C` is where the two come apart, and it is not invertible in the
cases that motivate an output — a projection onto the measured coordinates, a
sensor reading fewer numbers than the state carries.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]

theorem OutputEq.holds_of_outputSet (out : OutputEq 𝕋 n m r) (R : S n) (U : S m)
    (spec : Specification (Vec ℝ r)) {x : Vec ℝ n} {u : Vec ℝ m}
    (hx : x ∈ construct R) (hu : u ∈ construct U)
    (h : spec.Holds (construct (out.outputSet R U))) : spec.Holds {out.eval x u} :=
  spec.holds_of_outer (Set.singleton_subset_iff.mpr (out.outputSet_outer R U hx hu)) h

end CORALean.Real
