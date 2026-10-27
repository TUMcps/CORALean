module

public import CORALean.ContSet.Zonotope.Float.Operations.AdaptSetOrderLoop

@[expose] public section

/-!
# `Alg. 3` in floats: the order to reduce the particular solution to

`Real.Zonotope.adaptSetOrder` computed in `𝕋`: the share `ε_S,max,i` of eq. (13) for a step of
length `Δt`, the loop from `param(PR)` (`Z.h`, which drops no generator), and the error `ε_S`
accumulates, eq. (12). The times and errors are ℚ, exact; the step is read back through `ToRat`.
Which order comes out affects how tight the result is, never whether it is sound: every order is a
`reduce`. A NaN `Δt` or `errOp` reads through `ToRat` as `1.5 · 2 ^ 1024`, which exhausts the budget
`ε_S` and keeps higher orders. The order and `ε_S` do not enter `adaptiveStepFloat_outer`, so a NaN
here costs tightness only.

## Inputs
* `Z` – zonotope to reduce
* `εSmax` – total error budget
* `εSacc` – error accumulated so far
* `tf` – final time
* `ti` – current time
* `Δt` – step length

## Output
* order to reduce to and the error that reduction accumulates

## References

* [1] [M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC),
      2020.](../../../../../../references/2020/wetzlinger-cdc-adaptive-tuning.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: the order to reduce `PR([0,t_{i+1}])` to, and the `ε_S` that
reduction accumulates. -/
def Zonotope.adaptSetOrder (Z : Zonotope (Vec 𝕋 n)) (εSmax εSacc tf ti : ℚ) (Δt : 𝕋) : ℕ × ℚ :=
  -- 1. the admissible share of the remaining budget, `ε_{S,i}`, eq. (13)
  let εSi := (εSmax - εSacc) / (tf - ti) * ToRat.toRat Δt
  -- 2. `Φ_set ← param(PR)`, reducing nothing
  let Φset := Z.h
  -- 3. lines 3-7: `decr` and `red` while the reduction is admissible
  let Φset' := Z.adaptSetOrderLoop εSi Φset Φset
  -- 8. accumulate the reduction's error, eq. (12)
  (Φset', εSacc + ToRat.toRat (Z.reduceGirardBox Φset').errOp)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
