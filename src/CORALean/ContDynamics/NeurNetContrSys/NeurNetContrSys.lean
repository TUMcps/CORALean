module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.NN.NeuralNetwork
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# A neural network in the loop of a plant: the representation

CORA's `neurNetContrSys(sys, nn, dt)`: one class over every plant CORA accepts, the network's
output `u = π(x(i Δtc))` computed at the sampling instants and *held* over the control period
`Δtc` (CORA's `dt`, here the argument of `Trajectory`). [1, Alg. 2]'s system
`ẋ(t) = f(x(t), u_c(x(t), t), w(t))`, with the disturbance `w(t) ∈ W`.

`Plant` is what the class asks of a plant: the `m` inputs the network drives, the `r` remaining
ones (CORA's external inputs `n_ext`, here the disturbance), and the right-hand side `f x u w`.
A `LinearSys` is `ẋ = A x + B u + c` (CORA's `aux_augmentLinear`), the network driving every
input, so `r = 0`; as in CORA, `E` and the output equation do not enter the loop. A
`NonlinearSys n (m + r)` is `ẋ = f(x, (u, w))`, CORA's `sys.mFile(x(1:n), [x(n+1:n+m); u])`.
The discrete-time loop is `NeurNetContrSysDT`, its runs indexed by `ℕ`.

`Trajectory` is stated per period, with the derivative taken *within that period*: at a sampling
instant `u` jumps and `x` is differentiable only one-sidedly. `H` bounds the number of periods.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n m r : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A plant a network can close the loop of: `m` inputs the network drives, `r` disturbance
inputs, and the right-hand side `f x u w`. -/
class NeurNetContrSys.Plant (P : Type) (n : outParam ℕ) where
  m : P → ℕ
  r : P → ℕ
  f : (p : P) → Vec ℝ n → Vec ℝ (m p) → Vec ℝ (r p) → Vec ℝ n

/-- A linear plant, `ẋ = A x + B u + c`: the network drives every input, no disturbance. -/
instance NeurNetContrSys.Plant.linearSys : NeurNetContrSys.Plant (LinearSys 𝕋 n) n where
  m p := p.m
  r _ := 0
  f p x u _ := toRealMat p.A *ᵥ x + (toRealMat p.B *ᵥ u + toRealVec p.c)

/-- A nonlinear plant, `ẋ = f(x, (u, w))`: the network drives the first `m` inputs, the
disturbance is the last `r`. -/
instance NeurNetContrSys.Plant.nonlinearSys :
    NeurNetContrSys.Plant (NonlinearSys n (m + r)) n where
  m _ := m
  r _ := r
  f p x u w := p.f x (Fin.append u w)

open NeurNetContrSys (Plant)

/-- The plant and the network controlling it. -/
structure NeurNetContrSys (P : Type) (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ)
    [Plant P n] where
  plant : P
  contr : NeuralNetwork S n (Plant.m plant)

/-- One run over `H` control periods of length `Δtc`: the input is `π(x(i Δtc))` on period `i`,
the disturbance stays in `W`, and `x` starts in `R₀`. `π` is what the controller computes,
which `NeuralNetwork` does not store. -/
structure NeurNetContrSys.Trajectory {P : Type} [Plant P n] (sys : NeurNetContrSys P S n)
    (π : Vec ℝ n → Vec ℝ (Plant.m sys.plant)) (Δtc : ℝ) (H : ℕ) (R₀ : S n)
    (W : S (Plant.r sys.plant)) (x : ℝ → Vec ℝ n) (w : ℝ → Vec ℝ (Plant.r sys.plant)) :
    Prop where
  init : x 0 ∈ construct R₀
  dist (t : ℝ) (ht : t ∈ Set.Icc 0 ((H : ℝ) * Δtc)) : w t ∈ construct W
  flow (i : ℕ) (hi : i < H) (t : ℝ)
      (ht : t ∈ Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) :
    HasDerivWithinAt x (Plant.f sys.plant (x t) (π (x ((i : ℝ) * Δtc))) (w t))
      (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
