module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.EmptyExact

@[expose] public section

/-!
# `Interval.empty` is exactly empty

`one` reads as `1` and `zero` as `0`, so the stored box is the exact layer's empty one.

## Inputs
* none

## Hypotheses
* `hn` – dimension positive

## Conclusion
* the empty box represents the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.empty_exact (hn : 0 < n) :
    (Interval.empty n : Interval (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  have h : (Interval.empty n : Interval (Vec 𝕋 n)).nominal = Real.Interval.empty n := by
    unfold Interval.nominal Interval.empty Real.Interval.empty
    congr 1
    · funext i; exact toReal_one
    · funext i; exact toReal_zero
  show (Interval.empty n : Interval (Vec 𝕋 n)).nominal.construct = ∅
  rw [h]
  exact Real.Interval.empty_exact hn


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
