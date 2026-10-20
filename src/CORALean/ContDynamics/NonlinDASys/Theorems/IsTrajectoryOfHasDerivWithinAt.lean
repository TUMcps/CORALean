module

public import CORALean.ContDynamics.NonlinDASys.NonlinDASys
public import CORALean.Global.AestronglyMeasurableOfHasDerivWithinAt
public import CORALean.Global.EqAddIntegralOfHasDerivWithinAt

@[expose] public section

/-!
# A classical run of the DAE is a Carathéodory run

As for `NonlinearSys`: a state with the derivative `f(x t, y t, u t)` within a convex `T ∋ 0` at
every point of `T`, the field along it integrable from `0`, satisfies the integral equation
`IsTrajectory` states; the derivative makes the field measurable on `T` and the state
continuous. The constraint is pointwise, the same in both readings.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – differential trajectory
* `y` – algebraic trajectory
* `u` – input signal

## Hypotheses
* `hTconv` – time set convex
* `h0T` – zero lies in the time set
* `init` – start lies in `R₀`
* `input` – inputs lie in `U`
* `hd` – the field is the derivative
* `hint` – the field is integrable
* `constraint` – the constraint holds

## Conclusion
* the classical run is a DAE trajectory
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n p m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with the field as its derivative everywhere on a convex `T ∋ 0` is a run. -/
theorem NonlinDASys.IsTrajectory.of_hasDerivWithinAt {sys : NonlinDASys n p m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {y : ℝ → Vec ℝ p} {u : ℝ → Vec ℝ m}
    (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T) (init : x 0 ∈ construct R₀)
    (input : ∀ t ∈ T, u t ∈ construct U)
    (hd : ∀ t ∈ T, HasDerivWithinAt x (sys.f (x t) (y t) (u t)) T t)
    (hint : ∀ t ∈ T, IntervalIntegrable (fun s => sys.f (x s) (y s) (u s)) volume 0 t)
    (constraint : ∀ t ∈ T, sys.g (x t) (y t) (u t) = 0) :
    sys.IsTrajectory T R₀ U x y u (fun t => sys.h (x t) (y t) (u t)) where
  init := init
  input := input
  meas := aestronglyMeasurable_of_hasDerivWithinAt hTconv hd
  integrable := hint
  cont t ht := (hd t ht).continuousWithinAt
  flow t ht := eq_add_integral_of_hasDerivWithinAt hTconv h0T hd ht (hint t ht)
  constraint := constraint
  output _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
