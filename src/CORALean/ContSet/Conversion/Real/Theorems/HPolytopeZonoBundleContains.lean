module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeZonoBundleExact
public import CORALean.ContSet.HPolytope.Real.Operations.IsLPCentre
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

Through the zonotope the box gives, then `Zonotope.zonoBundle` — the
single-member bundle, exact by `Set.iInter_const`. All the loss is the box
route's, so this is no worse than `HPolytope → Zonotope` already is.

`zonoBundleRows` is what CORA's `@polytope/zonoBundle` actually builds, and it loses nothing: for
every row `aᵢ` of `[A; Ae; -Ae]`, an orthogonal basis `Bᵢ` whose first axis is `aᵢ`
(`Bᵢ = gramSchmidt(aᵢ')`), and the box of the vertices `V` in the coordinates `Bᵢ` spans, mapped
back by `Bᵢ`. Each zonotope contains the polytope (it holds every vertex), and its first axis is
cut at the largest value of `aᵢ` over the vertices, which is at most the right-hand side: the
intersection is inside every halfspace, so it is the polytope. The vertex list `V` and the bases
`Bᵢ` are arguments, as `vertices(P)` and `gramSchmidt` are: the theorem takes a `V` that spans the
polytope and bases with `Bᵢ Bᵢᵀ = 1` and `aᵢ x = ‖aᵢ‖ (Bᵢᵀ x)₀`, which Gram-Schmidt of `aᵢ`
gives. (A zero row has `‖aᵢ‖ = 0` and constrains nothing.)
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
