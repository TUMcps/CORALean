import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
import CORALean.ContSet.ConPolyZono.Float.Operations.ConsPolyZonotope
import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
import CORALean.ContSet.Interval.Float.Operations.Plus

/-!
# `ConPolyZono.getSubset`, over a floating-point scalar

Factor `k` re-parametrized onto `cen ± rad`, as over ℝ: `PolyZonotope.getSubset` at the generator
block and at the constraint columns read as a polynomial zonotope. The two channels of the layer
pay as they are meant to: the rounding of the generators goes into the ambient error box, the
rounding of the constraint matrix into `b`, widened outward by the row radius of what the stored
entries lost.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.getSubset (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p) (cen rad : 𝕋) :
    ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := cPZ.p
  h := (cPZ.toPolyZonotope.getSubset k cen rad).h
  q := cPZ.q
  m := cPZ.m
  s := (cPZ.consPolyZonotope.getSubset k cen rad).h
  c := cPZ.c
  G := (cPZ.toPolyZonotope.getSubset k cen rad).G
  E := (cPZ.toPolyZonotope.getSubset k cen rad).E
  GI := cPZ.GI
  A := fun i l => (cPZ.consPolyZonotope.getSubset k cen rad).G l i
  -- the rounding of the stored constraint entries, scaled by monomials in `[-1, 1]`
  b := cPZ.b.plus (PolyZonotope.generatorError (cPZ.consPolyZonotope.getSubsetGDiff k cen rad))
  EC := (cPZ.consPolyZonotope.getSubset k cen rad).E
  err := (cPZ.toPolyZonotope.getSubset k cen rad).err

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
