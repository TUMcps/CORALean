module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMapDep

@[expose] public section

/-!
# `ConPolyZono.quadMap` over a floating-point scalar

CORA's `@conPolyZono/quadMap` on the stored floats: as over ℝ, the map is expanded on a set
whose coefficients are all dependent, here the float `PolyZonotope.dependent` of the generator
part, which also frees the error box into one fresh factor per coordinate; then the float
`PolyZonotope.quadMapDep`, each generator `Gᵢᵀ Q Gⱼ` rounded down and its gap to the rounded-up
one charged to the error box. The constraints are kept on the original factors, widened by zero
exponent rows for the fresh ones (`padE`), so a factor vector meets them exactly when its first
block does. Outer, never the exact image.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.quadMap (Q : Fin k → Mat 𝕋 n n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono
    𝕋 (Vec 𝕋 k) :=
  -- every coefficient dependent, the error box included
  let pZ := cPZ.toPolyZonotope.dependent
  -- the image of the generator part, its rounding in the error box
  let qZ := PolyZonotope.quadMapDep Q pZ
  { p := qZ.p, h := qZ.h, q := 0, m := cPZ.m, s := cPZ.s, c := qZ.c, G := qZ.G, E := qZ.E,
    GI := Fin.elim0, A := cPZ.A, b := cPZ.b,
    EC := Real.ConPolyZono.padE cPZ.EC (cPZ.q + n), I_error := qZ.I_error }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
