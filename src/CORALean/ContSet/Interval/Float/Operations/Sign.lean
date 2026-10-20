module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.sign`

CORA's `@interval/sign` is `interval(sign(I.inf), sign(I.sup))`. A float comparison certifies only
`≤` (`le`), so the bounds are read from the tests that can be certified: the lower bound is `0` when
`0 ≤ inf` is certified and `-1` otherwise, the upper bound `0` when `sup ≤ 0` is certified and `1`
otherwise. Equal to CORA's whenever the comparison is exact and the bound is nonzero, an enclosure
of
it otherwise.

## Inputs
* `I` – interval box

## Output
* box of coordinatewise signs
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.sign (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => if le zero (I.inf i) = true then zero else neg one
  sup := fun i => if le (I.sup i) zero = true then zero else one


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
