module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A run about a linearization point, as a linear run

The float reachability steps propagate `δ = x - x✱` rather than `x`: around the point `x✱`, `δ` is
a run of `ẋ = A δ + ũ` for any linear system `lsys` with system matrix `A`, under the input
`ũ(t) = f(x t, u t) - A (x t - x✱)`. The integrand of the linear integral equation is the
nonlinear one, `ũ` is measurable as the field less a continuous drift, and the sets are plain sets,
`(S := 𝒮)`: the start and the input set are what the step encloses them in, the run's own sets
being in whatever representation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n m : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x - x✱` is a run of `lsys`'s canonical form under `ũ = f(x, u) - A (x - x✱)`. -/
theorem NonlinearSys.IsTrajectory.linearize_sub {sys : NonlinearSys n m} {T : Set ℝ}
    {R₀ : S n} {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {lsys : LinearSys 𝕋 n}
    {xs : Vec ℝ n} {X₀ V : Set (Vec ℝ n)} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T R₀ U x u y)
    (hTm : MeasurableSet T) (h₀ : x 0 - xs ∈ X₀)
    (hV : ∀ t ∈ T, sys.f (x t) (u t) - toRealMat lsys.A *ᵥ (x t - xs) ∈ V) :
    lsys.IsCanonicalTrajectory (S := 𝒮) T X₀ V (fun t => x t - xs)
      (fun t => sys.f (x t) (u t) - toRealMat lsys.A *ᵥ (x t - xs)) where
  init := h₀
  input := hV
  meas := traj.meas.sub (((mulVecL (toRealMat lsys.A)).continuous.comp_continuousOn
    (traj.cont.sub continuousOn_const)).aestronglyMeasurable hTm)
  cont := traj.cont.sub continuousOn_const
  flow t ht := by
    simp only [add_sub_cancel]
    rw [traj.flow t ht]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
