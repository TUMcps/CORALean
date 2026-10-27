module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.TuneStepFloat

@[expose] public section

/-!
# `tuneStep` is complete in its fuel

If one of the first `fuel` halvings of `r₀` passes the float test, the search of [1]'s step
selector returns a step. Completeness is relative to the float test, as for the order selector.

## Inputs
* `nrm` – float norm bound
* `ε` – float admissible error
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the search returns a step when one of the halvings passes the float test

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Complete in its fuel: if one of the first `fuel` halvings of `r₀` passes the float test,
the search returns a step. -/
theorem MatExp.tuneStep_isSome {nrm ε : 𝕋} {η : ℕ} :
    ∀ (fuel : ℕ) (r₀ : 𝕋) (k : ℕ), k < fuel → MatExp.stepTest nrm ε η (half^[k] r₀) = true →
      (MatExp.tuneStep nrm ε η r₀ fuel).isSome = true
  | 0, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | f + 1, r₀, 0, _, ht => by
    rw [MatExp.tuneStep, if_pos (by simpa using ht)]; rfl
  | f + 1, r₀, k + 1, hk, ht => by
    rw [MatExp.tuneStep]
    split
    · rfl
    · exact MatExp.tuneStep_isSome f (half r₀) k (by omega)
        (by rwa [Function.iterate_succ_apply] at ht)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
