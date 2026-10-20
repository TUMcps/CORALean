module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# How far a pooled window may rise above its pivot, rounded up

Zero at the pivot, so the maximum is floored there and a stable window gets a gap of exactly
zero; every other tap's reach above the pivot's lower bound rounds up, `subUp`, and the exact
`maximumOver` above them. The one number max pooling rounds.

## Inputs
* `tap` – input index of every window position
* `p` – pivot position of every window
* `I` – box of the layer's input
* `j` – window index

## Output
* how far the window can rise above its pivot, rounded up
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Zero at the pivot, every other tap's reach rounded up. -/
def maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) : 𝕋 :=
  maximumOver fun l =>
    if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
