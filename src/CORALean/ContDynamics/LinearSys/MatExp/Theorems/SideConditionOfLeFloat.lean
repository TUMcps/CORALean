module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.OrderTestFloat
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The float side condition certified by `le` is the real one

`le`'s `true` is sound, `half` is exact and `nsmulDown` rounds the count down, so
`nrm ≤ (η + 2)/2` in the float reading gives `nrm / (η + 2) ≤ 1/2` in ℝ: the side condition
of the float remainder bound of [1]'s truncation order.

## Inputs
* `𝕋` – float type
* `nrm` – float norm bound
* `k` – order

## Hypotheses
* `h` – float comparison certifies the bound

## Conclusion
* the certified float condition implies the real side condition

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

open Matrix NormedSpace FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.sideCondition_of_le {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    {nrm : 𝕋} {k : ℕ}
    (h : le nrm (half (nsmulDown (k + 2) (one : 𝕋))) = true) : -- --- CONCL ---
    toReal nrm / ((k : ℝ) + 2) ≤ 1 / 2 := by -- --- PROOF ---
  have hle := toReal_le_of_le h
  have hcount := nsmulDown_le (k + 2) (one : 𝕋)
  rw [toReal_one, mul_one] at hcount
  rw [toReal_half] at hle
  have hpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast at hcount
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
