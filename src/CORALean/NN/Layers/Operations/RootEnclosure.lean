module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# The square root's machine enclosure

`sqrtDown` below, `sqrtUp` above, computed by `p` Newton steps
(`Global/Float/Sqrt`), sound for any `p`.

## Inputs
* `p` – number of Newton steps

## Output
* lower and upper bound of the square root
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sqrtDown` below, `sqrtUp` above, with `p` Newton steps. -/
def rootEnclosure (p : ℕ) : Enclosure 𝕋 where
  lo a := sqrtDown p a
  hi a := sqrtUp p a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
