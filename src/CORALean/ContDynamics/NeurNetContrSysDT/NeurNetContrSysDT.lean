import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.NN.NeuralNetwork

/-!
# A neural network in the loop of a discrete-time plant: the representation

CORA's `neurNetContrSys` at a `LinearSysDT`: the controller reads the state and
produces the input, `u(k) = π(x(k))`, and the plant advances
`x(k+1) = A x(k) + u(k)`. One controller invocation per plant step, so there is no
inter-sample behaviour to describe; `NeurNetContrSys` is the continuous-time loop.

No `B`. `LinearSysDT` carries only `A`, so the plant's input is already in state
coordinates and `B u` is `Layer.linear B 0`, exact at every representation the
controller's own linear layers already ask for.

The system is indexed by the set representation, which no other system class in
`ContDynamics` is. That is `Layer` carrying `enclose` and its soundness as
fields: a network is an object over a representation rather than a function.

`Trajectory` is the substantive departure from the rest of `ContDynamics`: there
is no input set and no free input, so a run is the orbit of `map` from a point of
`R₀`, which `Theorems.TrajectoryIterate` states rather than leaves implied.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NeurNetContrSysDT (𝕋 : Type) (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  plant : LinearSysDT 𝕋 n
  contr : NeuralNetwork S n n

/-- One step of the closed loop, and it is a function: the controller reads the
state, so nothing along a run is chosen. `π` is what the controller computes,
which `NeuralNetwork` no longer stores — `contr.Sound π` is what ties it back. -/
def NeurNetContrSysDT.map (sys : NeurNetContrSysDT 𝕋 S n) (π : Vec ℝ n → Vec ℝ n)
    (x : Vec ℝ n) : Vec ℝ n :=
  toRealMat sys.plant.A *ᵥ x + π x

/-- One admissible run. No `input` field and no input set: the only freedom is
the initial state. -/
structure NeurNetContrSysDT.Trajectory (sys : NeurNetContrSysDT 𝕋 S n)
    (π : Vec ℝ n → Vec ℝ n) (R₀ : S n) (x : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  step (k : ℕ) : x (k + 1) = toRealMat sys.plant.A *ᵥ x k + π (x k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
