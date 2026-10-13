import CORALean.ContSet.PolyZonotope.Float.Operations.SplitMany
import CORALean.ContSet.PolyZonotope.Float.Operations.ZonotopeCora
import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard
import CORALean.ContSet.Conversion.Float.Zonotope_to_HPolytope
import CORALean.ContSet.HPolytope.Float.Operations.ExcludesPoint

/-!
# `PolyZonotope.containsPointSet`, over a floating-point scalar

CORA's `@polyZonotope/containsPointSet`, as over ℝ: split the polynomial zonotope `splits` times
(`2^splits` pieces), enclose each piece, and the whole set, by a Girard-reduced zonotope converted
to a polytope, and report whether every point lies in at least one of these polytopes.

The polytope is the halfspace one, `Zonotope.hPolytope`, along the directions `dirs` proposes for
each reduced zonotope (its facet normals give CORA's `polytope(Z)`); every direction bounds the
zonotope with upward rounding, so the polytope encloses it whatever is proposed. A point counts
as outside a polytope only where `HPolytope.excludesPoint` certifies it, so the test is one-sided
in the same direction as over ℝ: a point set the polynomial zonotope contains is accepted, and
`false` proves some point is outside; `true` decides nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- No point is certified outside the polytopes of the reduced zonotopes of every piece and of
the set. -/
def PolyZonotope.containsPointSet [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope (Vec 𝕋 n)) {N : ℕ}
    (points : Fin N → Vec 𝕋 n) (splits order : ℕ)
    (dirs : Zonotope (Vec 𝕋 n) → Σ m, Mat 𝕋 m n) : Bool :=
  let pZsplit := pZ.splitMany splits
  -- polytope(reduce(zonotope(·), 'girard', order)), one per piece and one for `pZ`
  let poly : PolyZonotope (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) := fun q =>
    let Z := q.zonotopeCora.reduceGirard order
    Z.hPolytope (dirs Z).2
  let qZsplit : List (HPolytope 𝕋 (Vec 𝕋 n)) := pZsplit.map poly ++ [poly pZ]
  (List.finRange N).all fun i => qZsplit.any fun P => !P.excludesPoint (points i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
