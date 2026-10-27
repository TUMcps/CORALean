module

public import CORALean.NN.Layers.Definitions.Enclosure
public import CORALean.Global.Float.Exp

@[expose] public section

/-!
# The exponential enclosure

`Float.expDown` below, `Float.expUp` above, at reduction depth `k`. `expUp` bounds `exp a` only
for `a ≤ 2ⁿ/2`, so unlike the sigmoid, which gets both ends from `expDown`, the enclosure is not
total: `expRelaxation_enclosesWhere` asks of a box that its right end is under that bound.

## Inputs
* `k` – reduction depth

## Output
* enclosure of the exponential from the rounded bounds
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `expDown` below, `expUp` above, at reduction depth `k`. -/
def expEnclosure (k : ℕ) : Enclosure 𝕋 where
  enclose a := ⟨expDown k a, expUp k a⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
