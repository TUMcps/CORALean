module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `PolyZonotope.rmId`, over a floating-point scalar

CORA's `@polyZonotope/rmId`: the exponent rows of the listed factors are deleted, which pins
those factors at `1`. Center, generators and error box are copied, so nothing rounds. The
factors that stay are read off in order by `orderIsoOfFin`, as at the real layer.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` without the exponent rows of the factors in `S`. -/
def PolyZonotope.rmId (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    PolyZonotope (Vec 𝕋 n) where
  p := Sᶜ.card
  h := pZ.h
  q := pZ.q
  c := pZ.c
  G := pZ.G
  E := fun k => pZ.E (Sᶜ.orderIsoOfFin rfl k).1
  GI := pZ.GI
  I_error := pZ.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
