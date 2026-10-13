import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

/-!
# `SpectraShadow.map`

A linear map applies to centre and generators alike and leaves the inequality
alone, which is why a spectrahedral shadow is closed under one and why the shadow
needs nothing but the projection to be.

`mtimes` is this at `A *ᵥ ·`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.map (f : α →ₗ[ℝ] β) (S : SpectraShadow α) : SpectraShadow β where
  k := S.k
  m := S.m
  A₀ := S.A₀
  A := S.A
  c := f S.c
  G := fun j => f (S.G j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
