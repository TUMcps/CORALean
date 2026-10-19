module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.Global.AestronglyMeasurableOfHasDerivWithinAt
public import CORALean.Global.EqAddIntegralOfHasDerivWithinAt
public import CORALean.Global.IntervalIntegrableMulVecAddOfBounded

@[expose] public section

/-!
# Every classical run is a Carathéodory one

A run whose state has the derivative `A x + u` within `T` at every point of `T` — two-sided
wherever `T` is, so a zero-order-hold input, whose jumps have none, is no such run — satisfies
the integral equation `IsCanonicalTrajectory` states: the fundamental theorem of calculus, one
sided inside `T`. `T` convex and containing `0`, and `U` bounded, are what a window `[0, t] ⊆ T`
and its integrability cost; `u`'s measurability is the derivative's
(`aestronglyMeasurable_of_hasDerivWithinAt`), the drift `A x` being continuous. This is how a run
written down in closed form, a derivative at hand, is shown to be a run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run with the derivative `A x + u` everywhere on a convex `T ∋ 0`, under a bounded input
set, is a run. -/
theorem LinearSys.IsCanonicalTrajectory.of_hasDerivWithinAt {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} (hTconv : Convex ℝ T) (h0T : (0:ℝ) ∈ T)
    (hU : Bornology.IsBounded (construct U)) (init : x 0 ∈ construct R₀)
    (input : ∀ t ∈ T, u t ∈ construct U)
    (hd : ∀ t ∈ T, HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) T t) : -- --- CONCL ---
    sys.IsCanonicalTrajectory T R₀ U x u := by -- --- PROOF ---
  have hx : ContinuousOn x T := fun t ht => (hd t ht).continuousWithinAt
  have hm := aestronglyMeasurable_of_hasDerivWithinAt hTconv hd
  -- `u` is the derivative less the continuous drift `A x`
  have hAx : AEStronglyMeasurable (fun s => toRealMat sys.A *ᵥ x s) (volume.restrict T) :=
    ((mulVecL (toRealMat sys.A)).continuous.comp_continuousOn hx).aestronglyMeasurable
      hTconv.ordConnected.measurableSet
  have hu : AEStronglyMeasurable u (volume.restrict T) :=
    (hm.sub hAx).congr (Filter.Eventually.of_forall fun s => add_sub_cancel_left _ _)
  exact ⟨init, input, hu, hx, fun t ht => eq_add_integral_of_hasDerivWithinAt hTconv h0T hd ht
    (intervalIntegrable_mulVec_add_of_bounded hx hm input hU
      (hTconv.ordConnected.uIcc_subset h0T ht))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
