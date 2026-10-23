module

public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# An upper bound read as an extended real

The upper bound of an STL interval is stored as `WithTop 𝕋`, `⊤` for `inf`: read as an extended
real, `inf` is `⊤` and a stored bound is the real it denotes. The proof fields and the times of an
`STLInterval` are stated through it.

## Inputs
* `u` – upper bound

## Output
* the extended real it denotes
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `inf` is `⊤`, a stored bound the real it denotes. -/
noncomputable def STLInterval.toEReal (u : WithTop 𝕋) : EReal :=
  u.recTopCoe ⊤ fun x => ((toReal x : ℝ) : EReal)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
