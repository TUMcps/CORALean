module

public import CORALean.ContSet.ConPolyZono.Float.Operations.ToPolyZonotope
public import CORALean.ContSet.ConPolyZono.Float.Operations.ConsPolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Operations.GetSubset
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `ConPolyZono.getSubset`, over a floating-point scalar

Factor `k` re-parametrized onto `cen ± rad`, as over ℝ: `PolyZonotope.getSubset` at the generator
block and at the constraint columns read as a polynomial zonotope. The two channels of the layer
pay as they are meant to: the rounding of the generators goes into the ambient error box, the
rounding of the constraint matrix into the slack `b_error`, widened by the row radius of what the
stored entries lost.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
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
  -- the slack grows by the stored entries' rounding, scaled by monomials in `[-1, 1]`
  cons := ⟨cPZ.cons.m, (cPZ.consPolyZonotope.getSubset k cen rad).h,
    fun i l => (cPZ.consPolyZonotope.getSubset k cen rad).G l i,
    (cPZ.consPolyZonotope.getSubset k cen rad).E, cPZ.cons.b,
    fun i => addUp (absolute (cPZ.cons.b_error i))
      (radius (cPZ.consPolyZonotope.getSubsetGDiff k cen rad) i), cPZ.cons.op⟩
  cons_eq := cPZ.cons_eq
  I_error := (cPZ.toPolyZonotope.getSubset k cen rad).I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
