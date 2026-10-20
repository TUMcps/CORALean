module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Every run is a run of the canonical form

A run of `ẋ = A x + B u + c + E w` is a run of CORA's `canonicalForm` [1], `ẋ = A x + u'`, with
the combined input `u' = B u + c + E w`, wherever `U'` holds every value it takes: the integrand
is the same sum, bracketed differently. So whatever is proved of `IsCanonicalTrajectory` at an
input set `U' ⊇ B U ⊕ c ⊕ E W`, which `canonicalForm` computes, holds of every run of the full
system. The output equation plays no part: the canonical form keeps the state.

## Inputs
* `sys` – linear system
* `T` – time domain
* `X₀` – initial set
* `U` – input set
* `W` – disturbance set
* `V` – noise set
* `x` – state trajectory
* `u` – input signal
* `w` – disturbance signal
* `v` – noise signal
* `y` – output signal
* `U'` – combined input set

## Hypotheses
* `traj` – signal is a trajectory
* `hU'` – combined input lies in the combined set

## Conclusion
* the run is a canonical trajectory under the combined input

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The combined input `B u + c + E w` drives the canonical form along the same state. -/
theorem LinearSys.IsTrajectory.canonical {sys : LinearSys 𝕋 n} {T : Set ℝ} {X₀ : S n}
    {U : S sys.m} {W : S sys.r} {V : S sys.s} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ sys.m}
    {w : ℝ → Vec ℝ sys.r} {v : ℝ → Vec ℝ sys.s} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory T X₀ U W V x u w v y) {U' : S n}
    (hU' : ∀ t ∈ T,
      toRealMat sys.B *ᵥ u t + toRealVec sys.c + toRealMat sys.E *ᵥ w t ∈ construct U') :
    sys.IsCanonicalTrajectory T X₀ U' x
      (fun t => toRealMat sys.B *ᵥ u t + toRealVec sys.c + toRealMat sys.E *ᵥ w t) where
  init := traj.init
  input := hU'
  -- a matrix is continuous, so it keeps the input and the disturbance measurable
  meas := (((continuous_const.matrix_mulVec continuous_id).comp_aestronglyMeasurable
    traj.meas).add aestronglyMeasurable_const).add
    ((continuous_const.matrix_mulVec continuous_id).comp_aestronglyMeasurable traj.measDist)
  cont := traj.cont
  -- the same integrand, bracketed as `A x + (B u + c + E w)`
  flow t ht := by
    rw [traj.flow t ht]
    simp only [add_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
