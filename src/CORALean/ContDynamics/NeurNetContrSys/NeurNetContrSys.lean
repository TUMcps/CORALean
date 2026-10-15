module

public import CORALean.ContDynamics.Interfaces
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a plant: the representation

CORA's `neurNetContrSys(sys, nn, dt)`: one class over every plant, any `ContDynamics`, the
network's output `u = π(x(i dt))` computed at the sampling instants and *held* over the control
period `dt`, stored in the system as CORA stores it. [1, Alg. 2]'s system
`ẋ(t) = f(x(t), u_c(x(t), t), w(t))`, with the disturbance `w(t) ∈ W`.

The network drives the first `m` inputs of the plant, `m ≤ nrOfInputs`; the remaining
`nExt = nrOfInputs − m` are external, CORA's `n_ext`, and range over `U_ext`, CORA's `params.U` of
the closed system. The plant receives `U_nn × U_ext` (`inputSet`), its input vector being `[a; e]`
(`input`): in a run `U_nn` is the held `{π(x(i dt))}` and `e` the external signal `v`. With
`nExt = 0` (`ofFull`) the network drives every input. The plant's disturbance
(`nrOfDisturbances`) is the loop's; CORA's loop at a linear plant drops `E`, so its reachability
there is stated for a `W` that `E` sends to `0`. The discrete-time loop is `NeurNetContrSysDT`.

The run is `IsTrajectory`, in its own file for it is stated with `input` and `inputSet`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling its first `m` inputs, the rest external, and the control
period `dt`: CORA's `neurNetContrSys(sys, nn, dt)`. -/
structure NeurNetContrSys (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamics P n] where
  plant : P
  m : ℕ
  hm : m ≤ nrOfInputs plant
  contr : NeuralNetwork S n m
  dt : ℝ

/-- CORA's `n_ext`: the plant's inputs the network does not drive. -/
abbrev NeurNetContrSys.nExt (sys : NeurNetContrSys P S n) : ℕ := nrOfInputs sys.plant - sys.m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
