import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# How many squarings a window's exponential needs

`e^{At} = (e^{A t/2^s})^{2^s}`, and `half` is exact, so the range `[tLo, tHi]`
scales to `[tLo/2^s, tHi/2^s]` without rounding. This picks the first `s` at
which the scaled interval matrix's float norm bound is at most the step's own,
`normUpperBound([Δt, Δt] · A)`, and admissible at `η`: the Taylor enclosure
at the scaled range is then as tight as the step's, and sound. `s ≈ log₂ k` at
`t_k = k Δt`. The first test is precision, the second soundness; both are
certified by `le`. `none` if no `s < 128` passes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `s < 128` with `[tLo/2^s, tHi/2^s] · A` no larger in norm than
`[Δt, Δt] · A` and admissible at order `η`. -/
def LinearSys.squaringsFloat (sys : LinearSys 𝕋 n) (Δt tLo tHi : 𝕋) (η : ℕ) : Option ℕ :=
  let nrmΔt := MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A))  -- ≥ ‖Δt A‖
  (List.range 128).find? fun s =>
    let nrm := MatExp.normUpperBound                                  -- ≥ ‖t A‖ / 2^s
      (Interval.smul (half^[s] tLo) (half^[s] tHi) (Interval.point sys.A))
    le nrm nrmΔt && le nrm (half (nsmulDown (η + 2) one))             -- as tight, admissible

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
