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

/-- The soundness half of vertex enumeration: a list holding every point the
rows pin down encloses the polytope. An implementation must then show it found
those points, never that its search was exhaustive in any other sense. -/
theorem HPolytope.contains_of_pinned (hc : IsCompact P.construct) (W : VPolytope (Vec ℝ n))
    (hW : ∀ x ∈ P.construct,
        (∀ d : Vec ℝ n, (∀ i, P.A i x = P.b i → P.A i d = 0) → (∀ i, P.Ae i d = 0) → d = 0) →
        x ∈ Set.range W.V) : -- --- CONCL ---
    P.construct ⊆ W.construct := by -- --- PROOF ---
  have hext : P.construct.extremePoints ℝ ⊆ Set.range W.V := fun x hx =>
    hW x hx.1 fun _ h₁ h₂ => P.eq_zero_of_extremePoint hx h₁ h₂
  have hclosed : IsClosed (convexHull ℝ (Set.range W.V)) :=
    (Set.Finite.isCompact_convexHull ℝ (Set.finite_range W.V)).isClosed
  calc P.construct = closure (convexHull ℝ (P.construct.extremePoints ℝ)) :=
        (closure_convexHull_extremePoints hc P.convex_construct).symm
    _ ⊆ closure (convexHull ℝ (Set.range W.V)) := closure_mono (convexHull_mono hext)
    _ = convexHull ℝ (Set.range W.V) := hclosed.closure_eq
    _ = W.construct := W.construct_eq_convexHull.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
