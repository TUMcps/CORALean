module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# `Capsule.plusVec`

CORA's `@capsule/plus.m` with a vector: a capsule plus a vector is a capsule, the center shifted,
generator and radius unchanged.

## Inputs
* `C` – capsule
* `v` – translation

## Output
* `C` shifted by `v`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Capsule plus vector: the center shifted, generator and radius unchanged. -/
def Capsule.plusVec (C : Capsule n) (v : Vec ℝ n) : Capsule n := ⟨C.c + v, C.g, C.r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
