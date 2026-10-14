module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.NN.NeuralNetwork
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# A neural network in the loop of a continuous-time plant: the representation

CORA's `neurNetContrSys`: a `LinearSys` whose input is produced by a network at
discrete sampling instants and *held* between them, `u = π(x(i Δtc))` over period `i`. The
control period `Δtc` (CORA's `dt`, here the argument of `Trajectory`) is not the reachability
step; `Operations` is where the two meet, as `Δtc = N Δt`.

`flow` is stated per period, with the derivative taken *within that period*: at
a sampling instant `u` jumps and `x` is differentiable only one-sidedly, so a
derivative-everywhere run on `Ici 0` would force the input never to switch.
Restricted to one closed period the derivative is exactly right; `Theorems.Period` reads a
period as a `LinearSys.CanonicalClassicalTrajectory`, the only place the two developments touch.

`H` bounds the number of periods. The plant runs by its own `ẋ = A x + B u + c`: CORA's
closed loop `aux_augmentLinear`, the state `[x; u]` under `[A B; 0 0]` and `c`. The network's
outputs are all of the plant's inputs; CORA's extra external inputs (`n_ext`) are not
modelled, and, as in CORA, `E` and the output equation do not enter the loop.
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

structure NeurNetContrSys (𝕋 : Type) (S : ℕ → Type)
    [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) where
  plant : LinearSys 𝕋 n
  contr : NeuralNetwork S n plant.m

/-- One admissible run over `H` control periods of length `Δtc`. The input is
`π(x(i Δtc))` on period `i` — a closed loop, not a set of admissible inputs —
and `π` is what the controller computes, which `NeuralNetwork` does not store. -/
structure NeurNetContrSys.Trajectory (sys : NeurNetContrSys 𝕋 S n)
    (π : Vec ℝ n → Vec ℝ sys.plant.m) (Δtc : ℝ) (H : ℕ)
    (R₀ : S n) (x : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  flow (i : ℕ) (hi : i < H) (t : ℝ) (ht : t ∈ Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) :
    HasDerivWithinAt x
      (toRealMat sys.plant.A *ᵥ x t +
        (toRealMat sys.plant.B *ᵥ π (x ((i : ℝ) * Δtc)) + toRealVec sys.plant.c))
      (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
