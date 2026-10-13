import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStepOrderFloat

/-!
# `Alg. 2` lines 3-12 in floats: the step-size sweep

[1, Alg. 2]'s `adaptTimeStepSearch` computed in `𝕋`: shrink `Δt_i` by `μ` until some order
clears both bounds, the admissible share `ε_P,max,i` of eq. (10) recomputed in
ℚ at each new `Δt_i`, read back through `ToRat`. [1]'s loop has no iteration
bound, so `fuel` is an argument and the result an `Option`.

Tuning only: `adaptiveStepFloat` re-checks the step and order it is given, and
`adaptiveStepFloat_outer` holds for any. A NaN read through `ToRat` is `1.5 · 2 ^ 1024`.
A NaN `Δt` inflates the share `ε_P,max,i` and may be accepted here,
but `adaptiveStepFloat` refuses it.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 3-12: shrink `Δt_i` by `μ` until some order clears both bounds,
returning the step, the order and its `ε_H` and `ε_P`. -/
def LinearSys.adaptTimeStepSearchFloat (sys : LinearSys 𝕋 n) (eAt : Interval (Mat 𝕋 n n))
    (X₀ U : Zonotope (Vec 𝕋 n)) (εHmax εPmax εPacc tf ti : ℚ) (μ : 𝕋) (ηmax : ℕ) :
    𝕋 → ℕ → Option (𝕋 × ℕ × ℚ × ℚ)
  | _, 0 => none
  | Δt, k + 1 =>
    let εPi := (εPmax - εPacc) / (tf - ti) * ToRat.toRat Δt         -- 2./7. eq. (10)
    match sys.adaptTimeStepOrderFloat eAt X₀ U εHmax εPi Δt 2 (ηmax - 1) with
    | some (η, εH, εP) => some (Δt, η, εH, εP)
    | none => sys.adaptTimeStepSearchFloat eAt X₀ U εHmax εPmax εPacc tf ti μ ηmax
        (mulDown Δt μ) k                                            -- 8. Δt_i ← Δt_i μ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
