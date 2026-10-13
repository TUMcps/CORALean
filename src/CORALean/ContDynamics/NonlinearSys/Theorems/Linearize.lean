module

public import CORALean.ContDynamics.NonlinearSys.Operations.Linearize
public import CORALean.ContDynamics.NonlinearSys.Theorems.LinInputOuter
public import CORALean.ContDynamics.NonlinearSys.Theorems.Restrict
public import CORALean.ContDynamics.LinearSys.Definitions.ClassicalTrajectory

@[expose] public section

/-!
# A nonlinear run is a linear run over a widened input

The handoff conservative linearization exists for: the same state function `x`,
the linear system `linearize A`, and the input signal
`ũ(t) = f(x(t), u(t)) - A x(t)`, which lies in `linInput` wherever the
certificate holds. The flow condition is then an identity — `A x + ũ = f(x,u)`
— and the run is a `LinearSys.ClassicalTrajectory`, handed on by `.trajectory`.

The confinement `hR` stays a hypothesis here, the certificate saying nothing
outside `R`. It is discharged one level up, by `confinement_of_subset`, from a
check on the computed sets — not by CORA's own check, which is circular.

`hR` is asked for on the time domain and nowhere else, which is why that domain
is a parameter: the linear run produced constrains its input on the same set, so
confinement over one step buys a linear run over one step —
`linearize_horizon`'s whole content.

This is the step [1, Sec. IV-A] takes by superposition.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every trajectory of `sys` confined to `R` over its own time domain is a
trajectory of `linearize A` over that same domain, with input in `linInput`. -/
theorem NonlinearSys.Trajectory.linearize {sys : NonlinearSys n m} {T : Set ℝ} {R₀ : S n}
    {U : S m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {A : Mat ℝ n n}
    {B : Mat ℝ n m} {xs : Vec ℝ n} {us : Vec ℝ m} {R : Set (Vec ℝ n)} {L : S n}
    (traj : sys.Trajectory T R₀ U x u)
    (cert : AbstractionError sys.f A B xs us R (construct U) L)
    (hR : ∀ t ∈ T, x t ∈ R) :
    (NonlinearSys.linearize A).ClassicalTrajectory T R₀ (linInput sys.f A B xs us U L) x
      (fun t => sys.f (x t) (u t) - A *ᵥ x t) where
  init := traj.init
  input t ht := linInput_outer cert (hR t ht) (traj.input t ht)
  flow t ht := by
    have he : toRealMat (NonlinearSys.linearize A).A *ᵥ x t
        + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t) := by
      show A *ᵥ x t + (sys.f (x t) (u t) - A *ᵥ x t) = sys.f (x t) (u t)
      abel
    show HasDerivWithinAt x (toRealMat (NonlinearSys.linearize A).A *ᵥ x t
      + (sys.f (x t) (u t) - A *ᵥ x t)) T t
    rw [he]
    exact traj.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
