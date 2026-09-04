import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.NN.NeuralNetwork

/-!
# A neural network in the loop of a continuous-time plant: the representation

CORA's `neurNetContrSys`: a `LinearSys` whose input is produced by a network at
discrete sampling instants and *held* between them, so `u` is constant at
`π(x(i Δtc))` for the whole period. The control period `Δtc` is not the
reachability step; `Operations` is where the two meet, as `Δtc = N Δt`.

`flow` is stated per period, with the derivative taken *within that period*. A
zero-order-hold run is generally **not** a `LinearSys.Trajectory` on a two-sided
domain: at a sampling instant `u` jumps and `x` is differentiable only one-sidedly
from each side, so a run on `Ici 0` would force the two derivatives to agree and
hence force the input never to switch. Restricted to one closed period the same
predicate is exactly right, the endpoints being where the derivative becomes
one-sided; `Theorems.Period` is that reading, and the only place the two
developments touch.

`H` bounds the number of periods asserted over. No `B`, for the reason
`NeurNetContrSysDT` gives: an actuation matrix is the controller's last layer.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure NeurNetContrSys (𝕋 : Type) (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  plant : LinearSys 𝕋 n
  contr : NeuralNetwork S n n

/-- One admissible run over `H` control periods of length `Δtc`. The input is
not a parameter: it is `π(x(i Δtc))` on period `i`, which is what makes this a
closed loop rather than a system with a set of admissible inputs. -/
structure NeurNetContrSys.Trajectory (sys : NeurNetContrSys 𝕋 S n) (Δtc : ℝ) (H : ℕ)
    (R₀ : S n) (x : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  flow (i : ℕ) (hi : i < H) (t : ℝ) (ht : t ∈ Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) :
    HasDerivWithinAt x
      (toRealMat sys.plant.A *ᵥ x t + sys.contr.eval (x ((i : ℝ) * Δtc)))
      (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) t

end CORALean.Real
