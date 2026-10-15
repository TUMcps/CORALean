module

public import CORALean.ContDynamics.Interfaces
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a plant: the representation

CORA's `neurNetContrSys(sys, nn, dt)`: one class over every plant, any `ContDynamics`, the
network's output `u = π(x(i Δtc))` computed at the sampling instants and *held* over the control
period `Δtc` (CORA's `dt`, here the argument of `Trajectory`). [1, Alg. 2]'s system
`ẋ(t) = f(x(t), u_c(x(t), t), w(t))`, with the disturbance `w(t) ∈ W`.

The network drives every input of the plant (`nrOfInputs`), and the plant's disturbance
(`nrOfDisturbances`) is the loop's: at a `LinearSys` `E w`, at a `NonlinParamSys` the parameter.
CORA's loop at a linear plant drops `E`; its reachability at one is stated for a `W` that `E`
sends to `0`. CORA also lets the network drive only the first inputs, the rest external; that
split is not modelled. The discrete-time loop is `NeurNetContrSysDT`, its runs indexed by `ℕ`.

`Trajectory` is stated per period, as a run of the plant on `[0, Δtc]` shifted to the period's
start: at a sampling instant `u` jumps, and a run is a run of the plant only within a period.
`H` bounds the number of periods.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- The plant and the network controlling it, which drives every input of the plant. -/
structure NeurNetContrSys (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [ContDynamics P n] where
  plant : P
  contr : NeuralNetwork S n (nrOfInputs plant)

/-- One run over `H` control periods of length `Δtc`: `x` starts in `R₀`, and on period `i` it is
a run of the plant under the held input `π(x(i Δtc))` and a disturbance in `W`. `π` is what the
controller computes, which `NeuralNetwork` does not store. -/
structure NeurNetContrSys.Trajectory (sys : NeurNetContrSys P S n)
    (π : Vec ℝ n → Vec ℝ (nrOfInputs sys.plant)) (Δtc : ℝ) (H : ℕ) (R₀ : S n)
    (W : Set (Vec ℝ (nrOfDisturbances sys.plant))) (x : ℝ → Vec ℝ n)
    (w : ℝ → Vec ℝ (nrOfDisturbances sys.plant)) : Prop where
  init : x 0 ∈ construct R₀
  flow (i : ℕ) (hi : i < H) :
    ContDynamics.Trajectory sys.plant (Set.Icc 0 Δtc) Set.univ Set.univ W
      (fun t => x ((i : ℝ) * Δtc + t)) (fun _ => π (x ((i : ℝ) * Δtc)))
      (fun t => w ((i : ℝ) * Δtc + t))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
