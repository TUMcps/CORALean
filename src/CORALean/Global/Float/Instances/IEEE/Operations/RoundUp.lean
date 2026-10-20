module

public import CORALean.Global.Float.Instances.IEEE.Operations.Basic

@[expose] public section

/-!
# Rounding onto the grid, up

`Dyadic.roundUp` at `gridShift` rather than `Dyadic.shift`: the ceiling is the floor of the
negation, taken `gridShift` bits right. The result has at most `p` bits, one more only when the
ceiling carries into the next power of two, and an exponent of at least `qmin`.

## Inputs
* `d` – dyadic with the format's mantissa width

## Output
* the dyadic ceiled onto the format's grid
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

def roundUp (d : Dyadic fmt.p) : IEEE fmt :=
  let k := gridShift d
  ⟨-(-d.mantissa / 2 ^ k), d.exponent + k⟩

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
