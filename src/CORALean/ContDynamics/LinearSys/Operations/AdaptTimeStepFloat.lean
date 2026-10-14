module

public import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepSearchFloat
public import CORALean.Global.Float.RatUp

@[expose] public section

/-!
# `Alg. 2` in floats: the step size and the truncation order for one step

`adaptTimeStep` computed in `𝕋`: enlarge the previous step by `1/μ`, clip it
to what is left of the horizon, then run `adaptTimeStepSearchFloat` and
accumulate `ε_P`, eq. (9). The clip is CORA's `maxTimeStep`, not [1]'s, whose
`Alg. 1` can step past `t_f`: `t_f - t_i` is exact in ℚ, and `ratUp` turns
it into a candidate. Nothing rests on the candidate being exact: the run reads
the step it took back through `ToRat`, and clips the window it reports.

Tuning only: `adaptiveStepFloat` re-checks the step and order it is given, and
`adaptiveStepFloat_outer` holds for any. A NaN read through `ToRat` is `1.5 · 2 ^ 1024`. The clip
replaces a NaN `Δt` by the horizon.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the step size, the truncation order, its `ε_H` and the
accumulated `ε_P` for step `i`, or `none` where `fuel` shrinkings did not suffice. -/
def LinearSys.adaptTimeStepFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
    (X₀ U : Zonotope (Vec 𝕋 n)) (εHmax εPmax εPacc tf ti : ℚ) (Δtprev μ : 𝕋) (ηmax fuel : ℕ) :
    Option (𝕋 × ℕ × ℚ × ℚ) :=
  -- 1. enlarge the previous step
  let Δt := divUp Δtprev μ
  let maxTimeStep : 𝕋 := ratUp (tf - ti)                            -- t_f - t_i, rounded up
  let Δt' := if ToRat.toRat Δt < tf - ti then Δt else maxTimeStep   -- clipped to the horizon
  match sys.adaptTimeStepSearchFloat eAt X₀ U εHmax εPmax εPacc tf ti μ ηmax Δt' fuel with
  | none => none
  -- 13. accumulate, eq. (9)
  | some (Δti, ηi, εH, εP) => some (Δti, ηi, εH, εPacc + εP)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
