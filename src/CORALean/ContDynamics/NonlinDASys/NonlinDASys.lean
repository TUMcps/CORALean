module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

/-!
# Continuous-time nonlinear differential-algebraic systems: the representation

CORA's `nonlinDASys`: `ẋ(t) = f(x(t), y(t), u(t))`, `0 = g(x(t), y(t), u(t))`, with `y` algebraic,
and the output equation `z = h(x, y, u)`. `n` states, `p` constraints (CORA's `nrOfConstraints`,
the dimension of `y`) and `m` inputs; the output dimension `q` is a field, as CORA's
`nrOfOutputs` is a property. Absent an output equation CORA's is the state, `h x y u = x`.
Time-invariant as CORA's is. The output of a run is `h (x t) (y t) (u t)`, a function of it,
so `IsTrajectory` does not repeat it.

A `IsTrajectory` is `(x, y, u)` with `x` differentiable along `f`, and the constraint holding on
all of `T`; there is no separate consistency condition on `y 0`, which the constraint at `0`
already imposes (`0 ∈ T` is the caller's). CORA assumes the system is of differentiation index 1,
that `∂g/∂y` is invertible along solutions; the class does not carry it, as CORA's does not, and
`IsIndex1` in `Definitions/` states it, to be assumed where a theorem needs it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinDASys (n p m : ℕ) where
  f : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ n
  g : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ p
  q : ℕ
  h : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ q

structure NonlinDASys.IsTrajectory (sys : NonlinDASys n p m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (y : ℝ → Vec ℝ p) (u : ℝ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (sys.f (x t) (y t) (u t)) T t
  constraint (t : ℝ) (ht : t ∈ T) : sys.g (x t) (y t) (u t) = 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
