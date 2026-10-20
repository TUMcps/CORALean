module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCenter
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIffRows
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.EnclosePointsOuter
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.VPolytope.Real.Theorems.VertexMem
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusIntervalExact
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A halfspace description as a bundle of one

Through the zonotope the box gives, then `Zonotope.zonoBundle`, the single-member bundle, exact by
`Set.iInter_const`; all the loss is the box route's. `zonoBundleRows` is what CORA's
`@polytope/zonoBundle` builds, and it loses nothing: for every row `aᵢ` of `[A; Ae; -Ae]`, an
orthogonal basis `Bᵢ` whose first axis is `aᵢ` (`gramSchmidt(aᵢ')`), and the box of the vertices `V`
in the coordinates `Bᵢ` spans, mapped back by `Bᵢ`. Each zonotope contains the polytope, and its
first axis is cut at the largest value of `aᵢ` over `V`, at most the right-hand side, so the
intersection is the polytope. `V` and the `Bᵢ` are arguments, as `vertices(P)` and `gramSchmidt`
are.

## Inputs
* `up` – certified upper bound per coordinate
* `lo` – certified lower bound per coordinate

## Hypotheses
* none

## Conclusion
* polytope is contained in its zonotope bundle
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.zonoBundle_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.zonoBundle up lo).construct :=
  subset_trans (HPolytope.zonotope_contains up lo) (Zonotope.zonoBundle_exact _).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
