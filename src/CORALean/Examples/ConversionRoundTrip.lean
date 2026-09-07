import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.PolyZonotope_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_PolyZonotope

/-!
# Leaving a representation and coming back

What an operation implemented by conversion relies on and no single conversion
states: the two directions compose, so a set is still inside itself after a
round trip. Nothing is regained on the way back — an `_outer` step out is an
`_outer` step back — which is why these read `⊆` and never `=`.

Where the outward step is `_exact`, the round trip loses exactly what the
inward step loses and nothing more: `Zonotope → ConZonotope` and
`Zonotope → PolyZonotope` are equalities, so the width below is entirely the
other half's.

One use site per pair is what makes the conversion table a table rather than a
directory: these fail to compile if a conversion is renamed, retyped, or
restated in the other direction.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

-- Anonymous, since their content is that they elaborate.

/-- Out to a box and back: the widening is the bounding box, and the zonotope
that comes back is that box, not the one that went in. -/
example (Z : Zonotope (Vec ℝ n)) : Z.construct ⊆ Z.interval.zonotope.construct :=
  Z.interval_outer.trans (Interval.subset_zonotope Z.interval)

/-- Out to a zonotope and back: dropping the dependence between generators is
what widens, and the return is exact. -/
example (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.construct ⊆ pZ.zonotope.polyZonotope.construct :=
  pZ.zonotope_outer.trans (Zonotope.polyZonotope_exact pZ.zonotope).subset

/-- The same for a constrained zonotope, where dropping the constraints is the
widening and the return is again exact. -/
example (cZ : ConZonotope (Vec ℝ n)) :
    cZ.construct ⊆ cZ.zonotope.conZonotope.construct :=
  cZ.zonotope_outer.trans (Zonotope.conZonotope_exact cZ.zonotope).subset

end CORALean.Real
