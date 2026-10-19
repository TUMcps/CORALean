module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.ExcludesPoint
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.containsPointSet`, over a floating-point scalar

CORA's `@polyZonotope/containsPointSet`, as over ℝ: split the polynomial zonotope `splits` times
(`2^splits` pieces), enclose each piece by a Girard-reduced zonotope converted to a polytope, and
report whether every point lies in at least one of these polytopes. The reduced zonotope of the
whole set, which CORA's code appends, is not: see the ℝ file.

The polytope is the halfspace one, `Zonotope.hPolytope`, along the directions `dirs` proposes for
each reduced zonotope (its facet normals give CORA's `polytope(Z)`); every direction bounds the
zonotope with upward rounding, so the polytope encloses it whatever is proposed. A point counts
as outside a polytope only where `HPolytope.excludesPoint` certifies it, so the test is one-sided
in the same direction as over ℝ: a point set the polynomial zonotope contains is accepted, and
`false` proves some point is outside; `true` decides nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No point is certified outside the polytopes of the reduced zonotopes of every piece. -/
def PolyZonotope.containsPointSet [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope (Vec 𝕋 n)) {N : ℕ}
    (points : Fin N → Vec 𝕋 n) (splits order : ℕ)
    (dirs : Zonotope (Vec 𝕋 n) → Σ m, Mat 𝕋 m n) : Bool :=
  let pZsplit := pZ.splitMany splits
  -- polytope(reduce(zonotope(·), 'girard', order)), one per piece
  let poly : PolyZonotope (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) := fun q =>
    let Z := q.zonotope.reduceGirard order
    Z.hPolytope (dirs Z).2
  let qZsplit : List (HPolytope 𝕋 (Vec 𝕋 n)) := pZsplit.map poly
  (List.finRange N).all fun i => qZsplit.any fun P => !P.excludesPoint (points i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
