module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Le
public import CORALean.Global.Float.Instances.IEEE.IEEE

@[expose] public section

/-!
# Whether a value is past the format's range

The exponent here is unbounded, so a rounded result above `maxFinite` is kept where the format
would hold `±∞` (IEEE 754) or have no code at all (E4M3, E2M1). This is how that is detected:
`|x| > maxFinite`, compared exactly as `Dyadic.le` compares, at the common exponent.

## Inputs
* `x` – format value

## Output
* whether the value's magnitude exceeds the largest finite number
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

def overflows (x : IEEE fmt) : Bool :=
  !Dyadic.le (⟨x.mantissa.natAbs, x.exponent⟩ : Dyadic fmt.p)
    ⟨fmt.maxSignificand, fmt.emax - fmt.p + 1⟩

end IEEE

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
