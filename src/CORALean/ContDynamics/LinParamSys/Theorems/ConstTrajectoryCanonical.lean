module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Every constant-parameter run is a run of the canonical form

A run of `ẋ = A x + B u + c`, `A` fixed in the set, is a run of the canonical form
`ẋ = A x + u'` with the combined input `u' = B u + c`, wherever `U'` holds every value it takes:
the integrand is the same sum, bracketed differently. So whatever is proved of
`CanonicalConstTrajectory` at an input set `U' ⊇ B U ⊕ c` holds of every run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combined input `B u + c` drives the canonical form along the same state. -/
theorem LinParamSys.ConstTrajectory.canonical {sys : LinParamSys 𝕄 n} {T : Set ℝ} {X₀ : S n}
    {U : S sys.m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ sys.m} {A : Mat ℝ n n}
    (traj : sys.ConstTrajectory T X₀ U x u A) {U' : S n}
    (hU' : ∀ t ∈ T, sys.B *ᵥ u t + sys.c ∈ construct U') :
    sys.CanonicalConstTrajectory T X₀ U' x (fun t => sys.B *ᵥ u t + sys.c) A where
  init := traj.init
  input := hU'
  param := traj.param
  -- a matrix is continuous, so it keeps the input measurable
  meas := ((continuous_const.matrix_mulVec continuous_id).comp_aestronglyMeasurable
    traj.meas).add aestronglyMeasurable_const
  cont := traj.cont
  -- the same integrand, bracketed as `A x + (B u + c)`
  flow t ht := by
    rw [traj.flow t ht]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
