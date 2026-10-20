module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.lt`

The strict containment test at float, `ltStrict` for each bound: it asks for a positive margin, so
`true` is strict.

## Inputs
* `I` – first interval box
* `J` – second interval box

## Output
* `true` when each bound of `I` lies strictly inside `J`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.lt (I J : Interval (Vec 𝕋 n)) : Bool :=
  (List.finRange n).all fun j => ltStrict (J.inf j) (I.inf j) && ltStrict (I.sup j) (J.sup j)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
