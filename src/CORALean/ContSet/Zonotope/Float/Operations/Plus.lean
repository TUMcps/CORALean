module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual

@[expose] public section

/-!
# `Zonotope.plus`

Generators concatenate exactly, so only the center rounds and its `residual`
goes into the box, leaving the count at `h₁ + h₂` as over ℝ. Paying into new
generators instead would cost `n` more on every addition.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.plus (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) where
  h := Z₁.h + Z₂.h
  c := fun i => addDown (Z₁.c i) (Z₂.c i)
  G := Fin.append Z₁.G Z₂.G
  I_error := (Z₁.I_error.plus Z₂.I_error).plus (Zonotope.centerResidual Z₁.c Z₂.c)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
