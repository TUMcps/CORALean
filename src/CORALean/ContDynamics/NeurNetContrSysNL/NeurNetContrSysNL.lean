module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.NN.NeuralNetwork

@[expose] public section

/-!
# A neural network in the loop of a nonlinear plant: the representation

[1, Alg. 2]'s system: `ẋ(t) = f(x(t), u_c(x(t), t), w(t))` with the control input `u_c` produced by
a network at the sampling instants `iΔt` and held in between, disturbances `w(t) ∈ W`. The plant is
a `NonlinearSys` whose input stacks the control input and the disturbance, `f x (u, w)`; `contr` is
the network. A run holds `π(x(iΔt))` on period `i` and has the derivative of `x` taken *within that
period*, as `NeurNetContrSys.Trajectory` does: at a sampling instant `u` jumps and `x` is
differentiable only one-sidedly.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A nonlinear plant and the network controlling it. -/
structure NeurNetContrSysNL (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m r : ℕ) where
  plant : NonlinearSys n (m + r)
  contr : NeuralNetwork S n m

/-- One run over `H` control periods of length `Δtc`: the input is `π(x(i Δtc))` on period `i`,
the disturbance stays in `W`, and `x` starts in `R₀`. -/
structure NeurNetContrSysNL.Trajectory (sys : NeurNetContrSysNL S n m r)
    (π : Vec ℝ n → Vec ℝ m) (Δtc : ℝ) (H : ℕ) (R₀ : S n) (W : S r) (x : ℝ → Vec ℝ n)
    (w : ℝ → Vec ℝ r) : Prop where
  init : x 0 ∈ construct R₀
  dist (t : ℝ) (ht : t ∈ Set.Icc 0 ((H : ℝ) * Δtc)) : w t ∈ construct W
  flow (i : ℕ) (hi : i < H) (t : ℝ)
      (ht : t ∈ Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) :
    HasDerivWithinAt x (sys.plant.f (x t) (Fin.append (π (x ((i : ℝ) * Δtc))) (w t)))
      (Set.Icc ((i : ℝ) * Δtc) (((i : ℝ) + 1) * Δtc)) t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
