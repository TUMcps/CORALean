module

public import CORALean.ContSet.HPolytope.Real.Operations.TightAt
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPoint
public import CORALean.ContSet.HPolytope.Real.Operations.BasicPointTightAt
public import CORALean.ContSet.HPolytope.Real.Theorems.ExtremePoints
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.VPolytope.Real.Theorems.Basic
public import Mathlib.Analysis.Convex.KreinMilman
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope

@[expose] public section

/-!
# Halfspaces to vertices

`HPolytope.contains_vPolytope`: it contains its `vPolytope`.

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `hne` – polytope nonempty

## Conclusion
* vertex polytope is contained in the polytope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.contains_vPolytope (P : HPolytope (Vec ℝ n)) (hne : P.construct.Nonempty) :
    (P.vPolytope hne).construct ⊆ P.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ P.convex_construct
  rintro _ ⟨l, rfl⟩
  show (if P.basicPoint (signEquiv P.m l) ∈ P.construct then P.basicPoint (signEquiv P.m l)
    else hne.choose) ∈ P.construct
  split
  · assumption
  · exact hne.choose_spec

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
