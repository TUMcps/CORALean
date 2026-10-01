import CORALean.ContSet.SpectraShadow.Real.Operations.Map

/-!
# `SpectraShadow.mtimes`

CORA's `@spectraShadow/mtimes`: `map` at `A *ᵥ ·`, spelt with `*ᵥ` because that is
the form every caller states its matrix in. The matrices of the inequality are
untouched, so a singular `M` costs nothing, unlike a representation that stores
the set by its boundary.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
