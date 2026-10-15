module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Every run is a run of the canonical form

A run of `ẋ = A(t) x + B(t) u + c` is a run of the canonical form `ẋ = A(t) x + u'` with the
combined input `u' = B u + c`, wherever `U'` holds every value it takes: the integrand is the
same sum, bracketed differently. So whatever is proved of `IsCanonicalTrajectory` at an input set
`U' ⊇ B U ⊕ c` holds of every run, as CORA's `reach` hands its core `B U + c`; `inputSet` is
such a `U'`.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combined input `B u + c` drives the canonical form along the same state. -/
theorem LinParamSys.IsTrajectory.canonical {sys : LinParamSys 𝕄 n} {T : Set ℝ} {X₀ : S n}
    {U : S sys.m} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ sys.m} {A : ℝ → Mat ℝ n n}
    {B : ℝ → Mat ℝ n sys.m} (traj : sys.IsTrajectory T X₀ U x u A B) {U' : S n}
    (hU' : ∀ t ∈ T, B t *ᵥ u t + sys.c ∈ construct U') :
    sys.IsCanonicalTrajectory T X₀ U' x (fun t => B t *ᵥ u t + sys.c) A where
  init := traj.init
  input := hU'
  param := traj.param
  -- a measurable matrix times a measurable input is measurable
  meas := ((continuous_fst.matrix_mulVec continuous_snd).comp_aestronglyMeasurable
    (traj.measParamB.prodMk traj.meas)).add aestronglyMeasurable_const
  measParam := traj.measParam
  cont := traj.cont
  -- the same integrand, bracketed as `A x + (B u + c)`
  flow t ht := by
    rw [traj.flow t ht]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
