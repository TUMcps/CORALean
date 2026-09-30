import CORALean.Global.Float.Instances.Dyadic.Dyadic

/-!
# A dyadic as an exact rational

`m · 2 ^ e` evaluated in ℚ, where the power of two is exact for either sign of
`e`: the decoding `ToRat` asks for, shared by every format stored as a dyadic —
`IEEE`, `Flint` and the native binary64 through its bit decoding.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `m · 2 ^ e`, in ℚ. -/
def Dyadic.toRat {p : ℕ} (d : Dyadic p) : ℚ := (d.mantissa : ℚ) * 2 ^ d.exponent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
