module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Every run is a run of the canonical form

A run of `ẋ = A(t) x + B u + c` is a run of the canonical form `ẋ = A(t) x + u'` with the
combined input `u' = B u + c`, wherever `U'` holds every value it takes: the integrand is the
same sum, bracketed differently. So whatever is proved of `CanonicalTrajectory` at an input set
`U' ⊇ B U ⊕ c` holds of every run, as CORA's `reach` hands its core `B U + c`.
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
theorem LinParamSys.Trajectory.canonical {sys : LinParamSys 𝕄 n} {T : Set ℝ} {X₀ : S n}
    {U : S sys.m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ sys.m} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T X₀ U x u A) {U' : S n}
    (hU' : ∀ t ∈ T, sys.B *ᵥ u t + sys.c ∈ construct U') :
    sys.CanonicalTrajectory T X₀ U' x (fun t => sys.B *ᵥ u t + sys.c) A where
  init := traj.init
  input := hU'
  param := traj.param
  -- a matrix is continuous, so it keeps the input measurable
  meas := ((continuous_const.matrix_mulVec continuous_id).comp_aestronglyMeasurable
    traj.meas).add aestronglyMeasurable_const
  measParam := traj.measParam
  cont := traj.cont
  -- the same integrand, bracketed as `A x + (B u + c)`
  flow t ht := by
    rw [traj.flow t ht]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
