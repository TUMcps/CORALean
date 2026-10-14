module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.ofPoint`, over a floating-point scalar

A point as an ellipsoid with no generators: the centre stored as given, the error box at zero.
Nothing is computed, so nothing rounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.ofPoint (p : Vec 𝕋 n) : Ellipsoid 𝕋 n where
  k := 0
  q := p
  G := fun _ j => j.elim0
  err := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
