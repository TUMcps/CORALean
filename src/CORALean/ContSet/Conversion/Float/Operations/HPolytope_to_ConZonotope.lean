module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Operations.AnchorSlab
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar

A polytope whose error box is certified empty carries its equalities onto the coefficients too,
between the two bounds the rounding of the carried product allows, kept as equalities where
`ConZonotope.anchorSlab` certifies them; one with an error box is carried with the box folded
into its rows (`absorbRounding`), each equality as the two inequalities it stands for.

## Inputs
* `P` – halfspace polytope
* `Z` – zonotope

## Output
* inequality rows on the coefficients, widened by rounding
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inequality rows, carried onto the coefficients and widened by what carrying them rounds
off. -/
def HPolytope.onCoefficients (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : HPolytope
    𝕋 (Vec 𝕋 Z.h) :=
  -- how far a row's carried product can be off
  let err := radius (matMulDiff P.A (fun i j => Z.G j i))
  HPolytope.ineqs (matMulDown P.A (fun i j => Z.G j i))
    fun i => addUp (subUp (P.b i) (dotDown (P.A i) Z.c)) (err i)

/-- The constrained zonotope on `Z` whose coefficients meet the carried rows, equalities
included when the polytope's box is certified empty. -/
def HPolytope.conZonotopeOf (P : HPolytope 𝕋 (Vec 𝕋 n)) (Z : Zonotope (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  if P.isErrFree then
    -- how far an equality's carried product can be off
    let errE := radius (matMulDiff P.Ae (fun i j => Z.G j i))
    ConZonotope.anchorSlab ⟨Z.h, Z.c, Z.G, P.onCoefficients Z, Z.I_error⟩
      (matMulDown P.Ae (fun i j => Z.G j i))
      (fun i => subDown (subDown (P.be i) (dotUp (P.Ae i) Z.c)) (errE i))
      (fun i => addUp (subUp (P.be i) (dotDown (P.Ae i) Z.c)) (errE i))
  else ⟨Z.h, Z.c, Z.G, P.absorbRounding.onCoefficients Z, Z.I_error⟩

-- with certificates in hand: a box from the bounds, a zonotope from the box, these rows on it
/-- The constrained zonotope of a halfspace description, built from the bounds `up` and `lo` on each
coordinate: the box they span as a zonotope, with the polytope's rows as the coefficient constraint.
-/
def HPolytope.conZonotope {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  P.conZonotopeOf (HPolytope.zonotope up lo)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
