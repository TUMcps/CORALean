module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.Global.AestronglyMeasurableOfHasDerivWithinAt
public import CORALean.Global.EqAddIntegralOfHasDerivWithinAt

@[expose] public section

/-!
# A classical constant-parameter run is a Carathéodory run

As for `NonlinearSys`: a state with the derivative `f(x t, u t, p)` within a convex `T ∋ 0` at
every point of `T`, the field along it integrable from `0`, satisfies the integral equation
`IsConstTrajectory` states; the derivative makes the field measurable on `T` and the state
continuous.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with the field at `p` as its derivative everywhere on a convex `T ∋ 0` is a run. -/
theorem NonlinParamSys.IsConstTrajectory.of_hasDerivWithinAt {sys : NonlinParamSys n m q}
    {T : Set ℝ} {R₀ : S n} {U : S m} {P : S q} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    {p : Vec ℝ q} (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T) (init : x 0 ∈ construct R₀)
    (input : ∀ t ∈ T, u t ∈ construct U) (param : p ∈ construct P)
    (hd : ∀ t ∈ T, HasDerivWithinAt x (sys.f (x t) (u t) p) T t)
    (hint : ∀ t ∈ T,
      IntervalIntegrable (fun s => sys.f (x s) (u s) p) volume 0 t) :
    sys.IsConstTrajectory T R₀ U P x u p (fun t => sys.g (x t) (u t) p) where
  init := init
  input := input
  param := param
  meas := aestronglyMeasurable_of_hasDerivWithinAt hTconv hd
  integrable := hint
  cont t ht := (hd t ht).continuousWithinAt
  flow t ht := eq_add_integral_of_hasDerivWithinAt hTconv h0T hd ht (hint t ht)
  output _ _ := rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
