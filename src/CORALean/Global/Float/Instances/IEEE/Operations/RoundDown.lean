module

public import CORALean.Global.Float.Instances.IEEE.Operations.GridShift

@[expose] public section

/-!
# Rounding onto the grid, down

Integer `/` floors for a positive divisor, so dropping `gridShift` bits and raising the
exponent to match rounds toward `-∞`, onto the grid of `fmt`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace IEEE

variable {fmt : IEEEFormat}


-- =====================================  MAIN DEFINITION  ====================================== --

def roundDown (d : Dyadic fmt.p) : IEEE fmt :=
  let k := gridShift d
  ⟨d.mantissa / 2 ^ k, d.exponent + k⟩

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
