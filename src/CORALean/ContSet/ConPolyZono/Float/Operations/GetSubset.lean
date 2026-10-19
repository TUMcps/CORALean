module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.PolyLevelSet.Float.Operations.GetSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.getSubset`, over a floating-point scalar

Factor `k` re-parametrized onto `cen ± rad`, as over ℝ: `PolyZonotope.getSubset` at the generator
block and the constraint's own `PolyLevelSet.getSubset`. The two channels of the layer pay as they
are meant to: the rounding of the generators goes into the ambient error box, the rounding of the
constraint matrix into the slack `b_error`, widened by the row radius of what the stored entries
lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.getSubset (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p) (cen rad : 𝕋) :
    ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p
  h := (cPZ.toPolyZonotope.getSubset k cen rad).h
  qI := cPZ.qI
  c := cPZ.c
  G := (cPZ.toPolyZonotope.getSubset k cen rad).G
  E := (cPZ.toPolyZonotope.getSubset k cen rad).E
  GI := cPZ.GI
  -- the rows re-parametrized, the slack widened by what their stored coefficients lost
  cons := cPZ.cons.getSubset k cen rad
  cons_eq := cPZ.cons_eq
  I_error := (cPZ.toPolyZonotope.getSubset k cen rad).I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
