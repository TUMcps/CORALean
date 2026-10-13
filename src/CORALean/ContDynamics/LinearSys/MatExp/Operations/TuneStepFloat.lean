module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.StepTestFloat

@[expose] public section

/-!
# `MatExp.tuneStep`, the step selector as a computable search

[1] shrinks the step `r` until the contribution `r · expRemainderBound (r • A) η` is within
the admissible error `ε`. `Real.MatExp.expRemainderStep` is that choice by `Classical.choose`
and does not run. This is the same choice as a halving search at a float representation:
`r₀, r₀/2, r₀/4, …` for at most `fuel` candidates (`half` is exact), stopping at the first
one that passes `stepTest`. A caller who runs out of fuel gets `none`.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first of `r₀, r₀/2, …` (at most `fuel` of them) passing `stepTest`, or `none`. -/
def MatExp.tuneStep (nrm ε : 𝕋) (η : ℕ) : 𝕋 → ℕ → Option 𝕋
  | _, 0 => none
  | r, k + 1 => if MatExp.stepTest nrm ε η r then some r else MatExp.tuneStep nrm ε η (half r) k

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
