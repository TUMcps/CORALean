import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.LinearSys
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# A time-varying run is a run at any frozen matrix, with the drift as input

`ConstTrajectory.toLinearSys` has no free counterpart at `'varParam'`: a run
drawing a fresh `A t` at every instant is a `LinearSys.Trajectory` for no matrix
at all, which is why the closed form never applied there. It is one at *every*
matrix `Â` once the mismatch is paid into the input —
`A t x + u = Â x + ((A t - Â) x + u)` — and that is what this states.

The price is `hV`: the input set has to hold the drift `(A t - Â) x t` as well
as `u t`, so it is a set the caller supplies and not `U`. That makes the
statement a conservative linearization in the parameter rather than an identity,
and the drift is bounded by `‖A t - Â‖ ‖x t‖`, which `Trajectory.norm_le`
bounds a priori.

`Â` need not lie in `construct sys.A`; the theorems that use this ask it
separately, being about the matrix set's own enclosures.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The time-varying reading at a frozen matrix: the parameter mismatch becomes
part of the input, and everything `LinearSys` proves applies again. -/
theorem LinParamSys.Trajectory.toLinearSys {sys : LinParamSys 𝕄 n} {T : Set ℝ}
    {R₀ U V : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T R₀ U x u A) (Â : Mat ℝ n n)
    (hV : ∀ t ∈ T, (A t - Â) *ᵥ x t + u t ∈ construct V) :
    (LinearSys.mk Â : LinearSys ℝ n).Trajectory T R₀ V x
      (fun t => (A t - Â) *ᵥ x t + u t) where
  init := traj.init
  input := hV
  flow := fun t ht => by
    -- the same vector field, split at `Â` rather than at `A t`
    have hsplit : Â *ᵥ x t + ((A t - Â) *ᵥ x t + u t) = A t *ᵥ x t + u t := by
      rw [Matrix.sub_mulVec]
      abel
    simpa only [Scalar.toRealMat_real, hsplit] using traj.flow t ht

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
