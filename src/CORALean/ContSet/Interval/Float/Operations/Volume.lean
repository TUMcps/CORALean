module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.volume` over floats

CORA's `volume_`, the product of the widths, as an upper bound: each width rounded up and clipped at
zero (a crossed coordinate denotes `∅` and counts as `0`, as over ℝ), the product rounded up.

## Inputs
* `I` – interval box

## Output
* upper bound of the volume of the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def Interval.aux_widthUp (I : Interval (Vec 𝕋 n)) (i : Fin n) : 𝕋 :=
  maximum zero (subUp (I.sup i) (I.inf i))


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.volume (I : Interval (Vec 𝕋 n)) : 𝕋 := prodUp fun i => I.aux_widthUp i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
