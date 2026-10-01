import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# How many squarings a window's exponential needs, at every member

`LinearSys.squaringsFloat` at the system's interval matrix: the first `s < 128` at
which `[tLo/2^s, tHi/2^s] · sys.A` has a float norm bound no larger than the
step's `[Δt, Δt] · sys.A`, and admissible at `η`. `half` is exact, so the
scaled range is the range divided by `2^s`. The first test is precision, the
second soundness; `none` if no `s` passes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `s < 128` with `[tLo/2^s, tHi/2^s] · sys.A` no larger in norm than
`[Δt, Δt] · sys.A` and admissible at order `η`. -/
def LinParamSys.squaringsFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (Δt tLo tHi : 𝕋) (η : ℕ) : Option ℕ :=
  let nrmΔt := MatExp.normUpperBound (Interval.smul Δt Δt sys.A)   -- ≥ ‖Δt A‖, every A ∈ sys.A
  (List.range 128).find? fun s =>
    let nrm := MatExp.normUpperBound                                  -- ≥ ‖t A‖ / 2^s
      (Interval.smul (half^[s] tLo) (half^[s] tHi) sys.A)
    le nrm nrmΔt && le nrm (half (nsmulDown (η + 2) one))             -- as tight, admissible

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
