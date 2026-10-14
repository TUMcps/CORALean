module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.point`, over a floating-point scalar

A single stored point: no generators and the error box at zero. Nothing is
computed, so nothing rounds — which is why this takes a stored point and the
exact layer's `ofPoint`, which asks for an arbitrary real one, has no float
counterpart.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.point (c : Vec 𝕋 n) : Zonotope (Vec 𝕋 n) where
  h := 0
  c := c
  G := fun j => j.elim0
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
