module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Continuous-time nonlinear differential-algebraic systems: the representation

CORA's `nonlinDASys`: `ẋ(t) = f(x(t), y(t), u(t))`, `0 = g(x(t), y(t), u(t))`, with `y` algebraic,
and the output equation `z = h(x, y, u)`. `n` states, `p` constraints and `m` inputs; the output
dimension `q` is a field. `IsTrajectory` is `(x, y, u)` with `x` a Carathéodory solution along
`f` as for `NonlinearSys`, and the constraint holding on all of `T`; a jumping input is
admissible, `y` jumping with it. [1, Eq. 1] states no solution concept beyond "unique
solutions"; its classical ones are among these. CORA assumes differentiation index 1, `∂g/∂y`
invertible along solutions; the class does not carry it, and `IsIndex1` in `Definitions/` states it.

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A nonlinear differential-algebraic system, as CORA's `nonlinDASys`: dynamics `f`, algebraic
constraint `g = 0` fixing the algebraic variables, and output `h` of dimension `q`. -/
structure NonlinDASys (n p m : ℕ) where
  f : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ n
  g : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ p
  q : ℕ
  h : Vec ℝ n → Vec ℝ p → Vec ℝ m → Vec ℝ q

/-- A Carathéodory run on `T`: the initial state lies in `R₀`, the inputs in `U`, the state
integrates `f`, the constraint `g = 0` holds at every instant, and the output follows `h`. -/
structure NonlinDASys.IsTrajectory (sys : NonlinDASys n p m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (y : ℝ → Vec ℝ p) (u : ℝ → Vec ℝ m) (z : ℝ → Vec ℝ sys.q) :
    Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable (fun t => sys.f (x t) (y t) (u t)) (volume.restrict T)
  integrable (t : ℝ) (ht : t ∈ T) :
    IntervalIntegrable (fun s => sys.f (x s) (y s) (u s)) volume 0 t
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, sys.f (x s) (y s) (u s)
  constraint (t : ℝ) (ht : t ∈ T) : sys.g (x t) (y t) (u t) = 0
  output (t : ℝ) (ht : t ∈ T) : z t = sys.h (x t) (y t) (u t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
