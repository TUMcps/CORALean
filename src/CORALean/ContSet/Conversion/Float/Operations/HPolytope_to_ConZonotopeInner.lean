module

public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# A halfspace description as a constrained zonotope from the inside, over a floating-point scalar

The inequality rows are carried onto the coefficients and tightened by what carrying them rounds
off, so every coefficient vector meeting the stored rows meets the exact ones. An equality leaves
no room to tighten into (a rounded one names another hyperplane, and a full-dimensional set has no
point on it), so a polytope with an equality is carried as the empty set, which is inside it. The
error box is not read by the rows: `conZonotopeInnerOf` carries it as the constrained zonotope's
own.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows carried onto the coefficients and *tightened* by what carrying them rounds off:
the opposite widening to `onCoefficients`. A polytope with an equality is carried as the empty
set. -/
def HPolytope.onCoefficientsInner (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : HPolytope
    𝕋 (Vec 𝕋 Z.h) :=
  if P.me = 0 then
    -- how far a row's carried product can be off
    let err := radius (matMulDiff P.A (fun i j => Z.G j i))
    { m := P.m
      A := matMulDown P.A (fun i j => Z.G j i)
      b := fun i => subDown (subDown (P.b i) (dotUp (P.A i) Z.c)) (err i)
      me := 0
      Ae := fun i => i.elim0
      be := fun i => i.elim0
      I_error := Interval.origin Z.h }
  else HPolytope.emptySet 𝕋 Z.h
/-- `{c + Gβ}` at the stored `c` and `G` of `Z`, with the rows of `P` tightened and the box of
`P` as its own error box: a constrained zonotope whose every point is a point of `P`, wherever
`Z` lies. -/
def HPolytope.conZonotopeInnerOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) where
  h := Z.h
  c := Z.c
  G := Z.G
  P := P.onCoefficientsInner Z
  I_error := P.I_error

/-- The tightened conversion of `P` at the box `Bx`, inside `P`: the box only decides how much of
`P` it covers, never whether it stays inside. -/
def HPolytope.conZonotopeInner (P : HPolytope 𝕋 (Vec 𝕋 n)) (Bx : Interval (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  P.conZonotopeInnerOf Bx.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
