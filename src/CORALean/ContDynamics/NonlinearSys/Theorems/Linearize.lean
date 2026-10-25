module

public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A nonlinear run is a linear run over a widened input

The handoff conservative linearization exists for: the same state function `x`, the linear system
`linearize A`, and the input signal `ũ(t) = f(x(t), u(t)) - A x(t)`, which lies in `linInput`
wherever the certificate holds. The integrand is then an identity, `A x + ũ = f(x,u)`, and the
run is a `LinearSys.IsCanonicalTrajectory`. The confinement `hR` stays a hypothesis, the
certificate saying nothing outside `R`; it is discharged one level up by `confinement_of_subset`,
from a check on the computed sets, not by CORA's own, circular check. This is the step
[1, Sec. IV-A] takes by superposition.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `x` – state trajectory
* `u` – input trajectory
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `R` – state region
* `L` – remainder set
* `y` – output trajectory

## Hypotheses
* `traj` – trajectory of the system
* `hTm` – time set measurable
* `cert` – abstraction-error certificate
* `hR` – trajectory stays in region

## Conclusion
* the trajectory is a linear trajectory over the widened input

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every trajectory of `sys` confined to `R` over its own time domain is a
trajectory of `linearize A` over that same domain, with input in `linInput`. -/
theorem NonlinearSys.IsTrajectory.linearize {sys : NonlinearSys n m} {T : Set ℝ} {R₀ : S n}
    {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n}
    {y : ℝ → Vec ℝ sys.q} (traj : sys.IsTrajectory T R₀ U x u y) (hTm : MeasurableSet T)
    (cert : IsAbstractionError sys.f A B xs us R (construct U) L)
    (hR : ∀ t ∈ T, x t ∈ R) :
    (NonlinearSys.linearize A).IsCanonicalTrajectory T R₀ (linInput sys.f A B xs us U L) x
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) where
  init := traj.init
  input t ht := linInput_outer cert (hR t ht) (traj.input t ht)
  meas := traj.meas.sub
    (((mulVecL A).continuous.comp_continuousOn traj.cont).aestronglyMeasurable hTm)
  cont := traj.cont
  flow t ht := by
    have he : (fun s => toRealMat (NonlinearSys.linearize A).A *ᵥ x s
        + (sys.f (x s) (u s) - A *ᵥ x s)) = fun s => sys.f (x s) (u s) := by
      funext s
      show A *ᵥ x s + (sys.f (x s) (u s) - A *ᵥ x s) = sys.f (x s) (u s)
      abel
    rw [he]
    exact traj.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
