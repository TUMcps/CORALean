import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixFloat
import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# The state differences a step spans, as a float zonotope

`deltaReach` computed in `𝕋`, CORA's `aux_deltaReach` at a zonotope:
`enclose(0, ([e^{AΔt}] - I) R) ⊕ [F] R`, every difference `x(t) - x(0)` of the
homogeneous flow over `t ∈ [0, Δt]`. `timeIntervalStepFloat` with the segment
anchored at the origin and the far end shifted, the same interval matrices, the
same correction matrix `[F]` covering the interpolation error.

At a zonotope the origin end is the generator-free zonotope at `0`, CORA's own
`zonotope.origin(n)` in the branch it takes for one; the `0 · D` the real layer
writes keeps factors only a polynomial zonotope has.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `enclose(0, ([e^{AΔt}] - I) R) ⊕ [F] R` at Taylor order `η`. -/
def LinearSys.deltaReachFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let eAΔt := sys.expIntervalFloat Δt Δt η                                  -- [e^{AΔt}]
  let F := MatExp.intervalCorrectionMatrix (Interval.point sys.A) Δt η      -- [F]
  let eAΔtI := Interval.matPlus eAΔt (Interval.point (negIdentityMat 𝕋 n))  -- [e^{AΔt}] - I
  let O := (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope           -- the origin
  LinComb.linComb O (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
    (S := fun k => Zonotope (Vec 𝕋 k)) eAΔtI R) ⊞
    Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- enclose(0, ·) ⊕ F R
      (S := fun k => Zonotope (Vec 𝕋 k)) F R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
