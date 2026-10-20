module

public import CORALean.ContSet.SpectraShadow.Real.Operations.Map

@[expose] public section

/-!
# `SpectraShadow.mtimes`

CORA's `@spectraShadow/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in. The matrices of the inequality are
untouched, so a singular `M` costs nothing, unlike a representation that stores
the set by its boundary.

## Inputs
* `M` – `m × n` matrix
* `S` – spectrahedral shadow

## Output
* the shadow with center and generators multiplied by `M` and the inequality kept
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.mtimes (M : Mat ℝ m n) (S : SpectraShadow (Vec ℝ n)) :
    SpectraShadow (Vec ℝ m) where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := M *ᵥ S.c
  G := fun j => M *ᵥ S.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
