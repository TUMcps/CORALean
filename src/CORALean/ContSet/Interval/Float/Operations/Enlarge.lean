module

public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.enlarge` over floats

CORA's `@interval/enlarge`: `[c - f·r, c + f·r]` for the center `c` and half-width `r`, scaled by a
nonnegative factor `f`. Each bound rounds outward: the lower one takes the center rounded down
(`centerLo`) less the product `f · r` rounded up, with `r` rounded up (`radius`); the upper one the
center rounded up (`center`) plus the same product.

## Inputs
* `I` – interval box
* `f` – enlargement factor

## Output
* box enlarged about its center by factor `f`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.enlarge (I : Interval (Vec 𝕋 n)) (f : 𝕋) : Interval (Vec 𝕋 n) :=
  let r : Vec 𝕋 n := fun i => mulUp f (I.radius i)
  ⟨fun i => subDown (I.centerLo i) (r i), fun i => addUp (I.center i) (r i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
