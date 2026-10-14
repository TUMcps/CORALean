module

public import CORALean.ContSet.Conversion.Float.HPolytope_to_ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A halfspace description as a constrained zonotope from the inside, over a floating-point scalar

`HPolytope.onCoefficientsInner`, `HPolytope.conZonotopeInnerOf` and `HPolytope.conZonotopeInner` are
the constructions; `HPolytope_to_ConZonotopeInner` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows carried onto the coefficients and *tightened* by what carrying them rounds off:
the opposite widening to `onCoefficients`, so every coefficient vector meeting the stored rows
meets the exact ones. -/
def HPolytope.onCoefficientsInner (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : HPolytope
    𝕋 (Vec 𝕋 Z.h) :=
  -- how far a row's carried product can be off, and the same for the equality rows
  let err := radius (matMulDiff P.A (fun i j => Z.G j i))
  let errE := radius (matMulDiff P.Ae (fun i j => Z.G j i))
  { m := P.m
    A := matMulDown P.A (fun i j => Z.G j i)
    b := fun i => subDown (subDown (P.b i) (dotUp (P.A i) Z.c)) (err i)
    me := P.me
    Ae := matMulDown P.Ae (fun i j => Z.G j i)
    be := ⟨fun i => addUp (subUp (P.be.inf i) (dotDown (P.Ae i) Z.c)) (errE i),
           fun i => subDown (subDown (P.be.sup i) (dotUp (P.Ae i) Z.c)) (errE i)⟩ }

/-- `{c + Gβ}` at the stored `c` and `G` of `Z`, with the rows of `P` tightened and no error box:
a constrained zonotope whose every point is a point of `P`, wherever `Z` lies. -/
def HPolytope.conZonotopeInnerOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) where
  h := Z.h
  c := Z.c
  G := Z.G
  P := P.onCoefficientsInner Z
  I_error := Interval.point fun _ => zero

/-- The tightened conversion of `P` at the box `Bx`, inside `P`: the box only decides how much of
`P` it covers, never whether it stays inside. -/
def HPolytope.conZonotopeInner (P : HPolytope 𝕋 (Vec 𝕋 n)) (Bx : Interval (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  P.conZonotopeInnerOf Bx.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
