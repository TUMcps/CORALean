module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.RoundAwayInt
public import CORALean.Global.Float.IntRound
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Interval.round`

CORA's `@interval/round` at its default of zero digits: both bounds go to the nearest integer,
halves away from zero. The scalar's exact rational (`ToRat`) is rounded as an integer
(`roundAwayInt`), and the integer enters the scalar by `intDown` for the lower bound and `intUp`
for the upper bound, so the box encloses the exact rounded box (an integer a scalar represents is
kept exactly).

## Inputs
* `I` – interval box

## Output
* box rounded outward to integers
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both bounds rounded to the nearest integer, the lower one down and the upper one up. -/
def Interval.round (I : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  ⟨fun i => intDown (roundAwayInt (ToRat.toRat (I.inf i))),
    fun i => intUp (roundAwayInt (ToRat.toRat (I.sup i)))⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
