module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar — the construction

`HPolytope.onCoefficients`, `HPolytope.conZonotopeOf` and `HPolytope.conZonotope` are the
constructions; `HPolytope_to_ConZonotope` states and proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows, carried onto the coefficients and widened by what carrying them
rounds off. -/
def HPolytope.onCoefficients (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : HPolytope
    𝕋 (Vec 𝕋 Z.h) :=
  -- how far a row's carried product can be off, and the same for the equality rows
  let err := radius (matMulDiff P.A (fun i j => Z.G j i))
  let errE := radius (matMulDiff P.Ae (fun i j => Z.G j i))
  { m := P.m
    A := matMulDown P.A (fun i j => Z.G j i)
    b := fun i => addUp (subUp (P.b i) (dotDown (P.A i) Z.c)) (err i)
    me := P.me
    Ae := matMulDown P.Ae (fun i j => Z.G j i)
    be := ⟨fun i => subDown (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c)) (errE i),
           fun i => addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c)) (errE i)⟩ }

def HPolytope.conZonotopeOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) where
  h := Z.h
  c := Z.c
  G := Z.G
  P := P.onCoefficients Z
  I_error := Z.I_error

-- with certificates in hand: a box from the bounds, a zonotope from the box, these rows on it
def HPolytope.conZonotope {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  P.conZonotopeOf (HPolytope.zonotope up lo)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
