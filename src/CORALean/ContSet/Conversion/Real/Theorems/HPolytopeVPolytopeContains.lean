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
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeContainsOfPinned

@[expose] public section

/-!
# Halfspaces to vertices

`HPolytope.vPolytope_contains`: its `vPolytope` contains it.

## Inputs
* `P` – halfspace polytope

## Hypotheses
* `hc` – polytope compact
* `hne` – polytope nonempty

## Conclusion
* polytope is contained in its vertex polytope
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

-- the other way: `contains_of_pinned` asks only that every extreme point be listed
theorem HPolytope.vPolytope_contains (P : HPolytope (Vec ℝ n)) (hc : IsCompact P.construct)
    (hne : P.construct.Nonempty) : -- --- CONCL ---
    P.construct ⊆ (P.vPolytope hne).construct := by -- --- PROOF ---
  refine HPolytope.contains_of_pinned hc _ fun x hx hpin => ?_
  refine ⟨(signEquiv P.m).symm (P.tightAt x), ?_⟩
  show (if P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) ∈ P.construct then
      P.basicPoint (signEquiv P.m ((signEquiv P.m).symm (P.tightAt x))) else hne.choose) = x
  rw [Equiv.apply_symm_apply, P.basicPoint_tightAt hx hpin, if_pos hx]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
