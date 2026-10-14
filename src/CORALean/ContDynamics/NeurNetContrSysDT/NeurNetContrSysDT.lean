module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a discrete-time plant: the representation

CORA's `neurNetContrSys` at a `LinearSysDT` [1]: the controller reads the state and
produces the plant's input, `u(k) = π(x(k))`, and the plant advances by its own equation,
`x(k+1) = A x(k) + B u(k) + c`: CORA's closed loop `aux_augmentLinear`, the augmented state
`[x; u]` with `[A B; 0 0]` and `c`, read one step at a time. One controller invocation per plant
step, so there is no inter-sample behaviour to describe; `NeurNetContrSys` is the
continuous-time loop. The network's outputs are all of the plant's inputs (`contr` ends in
`plant.m`); CORA's further external inputs (`n_ext`, the columns of `B` past the network's
outputs) are not modelled, and CORA's closed loop drops `E` and the output equation, as this
does.

The system is indexed by the set representation, which no other system class in
`ContDynamics` is: `Layer` carries `enclose` and its soundness as fields.

`Trajectory` is the substantive departure from the rest of `ContDynamics`: there
is no input set and no free input, so a run is the orbit of `map` from a point of
`R₀`, which `Theorems.TrajectoryIterate` states rather than leaves implied.

## References

* [1] `contDynamics/@neurNetContrSys/neurNetContrSys.m`, `aux_computeProperties`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
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
  contr : NeuralNetwork S n plant.m

/-- One step of the closed loop, and it is a function: the controller reads the
state, so nothing along a run is chosen. `π` is what the controller computes,
which `NeuralNetwork` no longer stores — `contr.Sound π` is what ties it back. -/
def NeurNetContrSysDT.map (sys : NeurNetContrSysDT 𝕋 S n) (π : Vec ℝ n → Vec ℝ sys.plant.m)
    (x : Vec ℝ n) : Vec ℝ n :=
  toRealMat sys.plant.A *ᵥ x + toRealMat sys.plant.B *ᵥ π x + toRealVec sys.plant.c

/-- One admissible run. No `input` field and no input set: the only freedom is
the initial state. -/
structure NeurNetContrSysDT.Trajectory (sys : NeurNetContrSysDT 𝕋 S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) (R₀ : S n) (x : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  step (k : ℕ) : x (k + 1) =
    toRealMat sys.plant.A *ᵥ x k + toRealMat sys.plant.B *ᵥ π (x k) + toRealVec sys.plant.c

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
