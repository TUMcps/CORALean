import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
import CORALean.ContDynamics.LinearSys.Operations.OneStep

/-!
# What makes a linearization sound for one run over one step

The hypotheses of `NonlinDASys.Trajectory.linReach_outer`, bundled for a `LinPoint`: a left
inverse `F⁻¹ F = I` of the constraint's `y`-block, a region `R^z` the run `(x, y, u)` stays in
over `[0, Δt]`, the two error zonotopes holding every consistent point's linearization errors
over `R^z`, `u* ∈ U`, `0 ∈ Verror`, and the step admissible for `oneStep` at order `q + 2`.
`initReach` asks it of the linearization of the part that holds the run's start.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` certifies the run `(x, y, u)` of `sys` from inputs in `U` over `[0, Δt]` at order
`q + 2`: the hypotheses `linReach_outer` takes, with `F` and `R^z` chosen. -/
def NonlinDASys.LinPoint.Certifies (L : NonlinDASys.LinPoint n p m) (sys : NonlinDASys n p m)
    (U : Zonotope (Vec ℝ m)) (Δt : ℝ) (q : ℕ) (x : ℝ → Vec ℝ n) (y : ℝ → Vec ℝ p)
    (u : ℝ → Vec ℝ m) : Prop :=
  ∃ (F : Mat ℝ p p) (Rz : Set (Vec ℝ n × Vec ℝ p × Vec ℝ m)),
    L.F_inv * F = 1 ∧ (∀ t ∈ Set.Icc 0 Δt, (x t, y t, u t) ∈ Rz) ∧
    (∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      (sys.f x' y' u' - (sys.f L.xs L.ys L.us + L.A *ᵥ (x' - L.xs) + L.B *ᵥ (u' - L.us)
        + L.C *ᵥ (y' - L.ys))) - (L.C * L.F_inv) *ᵥ (sys.g x' y' u' - (sys.g L.xs L.ys L.us
          + L.D *ᵥ (x' - L.xs) + L.E *ᵥ (u' - L.us) + F *ᵥ (y' - L.ys))) ∈ L.Verror.construct) ∧
    (∀ x' y' u', (x', y', u') ∈ Rz → sys.g x' y' u' = 0 →
      sys.g x' y' u' - (sys.g L.xs L.ys L.us + L.D *ᵥ (x' - L.xs) + L.E *ᵥ (u' - L.us)
        + F *ᵥ (y' - L.ys)) ∈ L.Verror_y.construct) ∧
    L.us ∈ U.construct ∧ (0 : Vec ℝ n) ∈ L.Verror.construct ∧
    ‖Δt • (L.A - L.C * L.F_inv * L.D)‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
