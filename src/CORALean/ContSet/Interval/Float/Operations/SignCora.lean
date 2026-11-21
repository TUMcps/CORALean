module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.signCora`

CORA's `sign` of a box: the sign of each bound, `[sign(inf), sign(sup)]`, which is exact since the
sign is monotone. A bound is `1` or `-1` only where the strict order certifies it and `0` only where
`le` certifies both directions; otherwise it falls back to the outer value (`-1` below, `1` above).
At `nearest` every test is the machine's, so this is CORA's result bit for bit.

## Inputs
* `I` – interval box

## Output
* the box of the signs of its bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `sign` of a box: `[sign(inf), sign(sup)]`, each sign certified or widened outward. -/
def Interval.signCora (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i =>
    if ltStrict zero (I.inf i) = true then one                                    -- inf > 0
    else if (le zero (I.inf i) && le (I.inf i) zero) = true then zero             -- inf = 0
    else neg one
  sup := fun i =>
    if ltStrict (I.sup i) zero = true then neg one                                -- sup < 0
    else if (le (I.sup i) zero && le zero (I.sup i)) = true then zero             -- sup = 0
    else one

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
