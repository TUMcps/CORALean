module

public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Theorems.IsClosed
public import CORALean.ContSet.HPolytope.Real.Theorems.Convex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section

/-!
# Halfspaces to vertices

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `hne` – polytope is nonempty

## Output
* vertex polytope listing one candidate per row subset
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One candidate per subset of the inequality rows, kept when feasible and
replaced by a point of the polytope when not — so every vertex listed is a point
of the polytope, which is what makes the conversion exact. -/
noncomputable def HPolytope.vPolytope (P : HPolytope (Vec ℝ n)) (hne : P.construct.Nonempty) :
    VPolytope (Vec ℝ n) where
  k := 2 ^ P.m
  V := fun l =>
    if P.basicPoint (signEquiv P.m l) ∈ P.construct then P.basicPoint (signEquiv P.m l)
    else hne.choose

/-- The cheap route: a box from `2n` certificates, then its corners. -/
noncomputable def HPolytope.vPolytopeBox
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : VPolytope (Vec ℝ n) :=
  Interval.vPolytope (HPolytope.interval up lo)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
