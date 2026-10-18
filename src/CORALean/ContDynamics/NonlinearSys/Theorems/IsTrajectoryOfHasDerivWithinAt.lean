module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys
public import CORALean.Global.AestronglyMeasurableOfHasDerivWithinAt
public import CORALean.Global.EqAddIntegralOfHasDerivWithinAt

@[expose] public section

/-!
# A classical run is a Carathéodory run

A state with the derivative `f(x t, u t)` within a convex `T ∋ 0` at every point of `T`, the
field along it integrable from `0`, satisfies the integral equation `IsTrajectory` states: the
fundamental theorem of calculus, one-sided inside `T`. The derivative makes the field
measurable on `T` and the state continuous, the rest of what a Carathéodory run asks.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with the field as its derivative everywhere on a convex `T ∋ 0` is a run. -/
theorem NonlinearSys.IsTrajectory.of_hasDerivWithinAt {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} (hTconv : Convex ℝ T)
    (h0T : (0:ℝ) ∈ T) (init : x 0 ∈ construct R₀) (input : ∀ t ∈ T, u t ∈ construct U)
    (hd : ∀ t ∈ T, HasDerivWithinAt x (sys.f (x t) (u t)) T t)
    (hint : ∀ t ∈ T, IntervalIntegrable (fun s => sys.f (x s) (u s)) volume 0 t) :
    sys.IsTrajectory T R₀ U x u (fun t => sys.g (x t) (u t)) where
  init := init
  input := input
  meas := aestronglyMeasurable_of_hasDerivWithinAt hTconv hd
  integrable := hint
  cont t ht := (hd t ht).continuousWithinAt
  flow t ht := eq_add_integral_of_hasDerivWithinAt hTconv h0T hd ht (hint t ht)
  output _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
