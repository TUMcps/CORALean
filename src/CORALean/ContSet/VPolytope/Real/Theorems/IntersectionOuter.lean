module

public import CORALean.ContSet.VPolytope.Real.Operations.Intersection
public import CORALean.ContSet.VPolytope.Real.Operations.EmptySet
public import CORALean.ContSet.VPolytope.Real.Theorems.ConstructEmptySet
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalHPolytopeExact
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeHPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact
public import CORALean.ContSet.VPolytope.Real.Operations.IntersectionH

@[expose] public section

/-!
# `VPolytope.intersection` contains the intersection

Both operands land in their own halfspace descriptions, intersection of
halfspace descriptions is exact, and vertex enumeration puts the result back —
or, when nothing is left, the empty vertex list already contains nothing.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope
* `Aq₁` – cut directions of the first operand
* `Aq₂` – cut directions of the second operand

## Hypotheses
* none

## Conclusion
* the intersection lies in the result
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   02-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n q₁ q₂ : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `VPolytope.intersectionH` is compact. -/
theorem VPolytope.aux_intersectionH_isCompact (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) :
    IsCompact (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct := by
  refine HPolytope.isCompact_of_contains (W := P₁.interval.vPolytope) fun x hx => ?_
  have h := (HPolytope.mem_intersection_iff.mp hx).2
  rw [Interval.hPolytope_exact] at h
  exact Interval.vPolytope_contains _ h


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intersection_outer (P₁ P₂ : VPolytope (Vec ℝ n))
    (Aq₁ : Fin q₁ → (Vec ℝ n →ₗ[ℝ] ℝ)) (Aq₂ : Fin q₂ → (Vec ℝ n →ₗ[ℝ] ℝ)) : -- --- CONCL ---
    P₁.construct ∩ P₂.construct ⊆ (P₁.intersection P₂ Aq₁ Aq₂).construct := by -- --- PROOF ---
  have hsub : P₁.construct ∩ P₂.construct ⊆ (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct := by
    rintro x ⟨hx₁, hx₂⟩
    refine HPolytope.mem_intersection_iff.mpr ⟨HPolytope.mem_intersection_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · exact P₁.hPolytope_contains Aq₁ hx₁
    · exact P₂.hPolytope_contains Aq₂ hx₂
    · rw [Interval.hPolytope_exact]
      exact P₁.interval_contains hx₁
  -- empty or not: an empty halfspace description leaves nothing to enumerate
  by_cases h : (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).construct.Nonempty
  · have he : P₁.intersection P₂ Aq₁ Aq₂
        = (VPolytope.intersectionH P₁ P₂ Aq₁ Aq₂).vPolytope h := dif_pos h
    rw [he]
    exact subset_trans hsub
      (HPolytope.vPolytope_contains _ (VPolytope.aux_intersectionH_isCompact P₁ P₂ Aq₁ Aq₂) h)
  · have he : P₁.intersection P₂ Aq₁ Aq₂ = VPolytope.emptySet (Vec ℝ n) := dif_neg h
    rw [he, VPolytope.construct_emptySet]
    rw [Set.not_nonempty_iff_eq_empty.mp h] at hsub
    exact hsub

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
