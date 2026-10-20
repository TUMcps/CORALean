module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OrderTestFloat

@[expose] public section

/-!
# `MatExp.tuneOrder`, the order selector as a computable search

[1] raises the Taylor order `η` from `2` until the remainder bound is within the admissible
error `ε`. `Real.MatExp.expRemainderOrder` names that choice as an infimum, which is
`Nat.find` under classical decidability and does not run. This is the same choice as a
search at a float representation: `η = 2, 3, …` for at most `fuel` orders, stopping at the
first one that passes `orderTest`. A caller who runs out of fuel gets `none`, never an
unchecked order.

## Inputs
* `nrm` – float norm bound
* `ε` – float admissible error
* `fuel` – number of orders tried

## Output
* first order passing the float test, if any

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

/-- The first order `η ∈ [2, 2 + fuel)` passing `orderTest`, or `none` if none does. -/
def MatExp.tuneOrder (nrm ε : 𝕋) (fuel : ℕ) : Option ℕ :=
  ((List.range fuel).map (2 + ·)).find? (MatExp.orderTest nrm ε)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
