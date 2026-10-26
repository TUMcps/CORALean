module

public import CORALean.ContSet.Polygon.Float.Operations.Basic
public import CORALean.ContSet.Polygon.Float.Operations.IntervalOfList
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.VPolytopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Polygon.interval` holds the polygon

Each piece's box holds it (`VPolytope.interval_contains`) and `Interval.or` holds both boxes.

## Inputs
* `P` – polygon

## Hypotheses
* none

## Conclusion
* `Polygon.interval` holds the polygon
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Polygon.aux_intervalOfList_contains :
    ∀ ps : List (VPolytope (Vec 𝕋 2)),
      (⋃ p ∈ ps, VPolytope.construct p) ⊆ (Polygon.intervalOfList ps).construct
  | [] => by simp
  | [p] => by
    intro x hx
    simp only [Set.mem_iUnion, List.mem_singleton, exists_prop, exists_eq_left] at hx
    exact VPolytope.interval_contains p hx
  | p :: q :: ps => by
    intro x hx
    have hrec := Polygon.aux_intervalOfList_contains (q :: ps)
    simp only [Set.mem_iUnion, List.mem_cons, exists_prop] at hx
    obtain ⟨s, hs | hs, hx⟩ := hx
    · subst hs
      exact Interval.or_outer _ _ (Or.inl (VPolytope.interval_contains _ hx))
    · refine Interval.or_outer _ _ (Or.inr (hrec ?_))
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨s, List.mem_cons.mpr hs, hx⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.interval_contains (P : Polygon 𝕋) :
    ContSet.construct P ⊆ (Polygon.interval P).construct :=
  Polygon.aux_intervalOfList_contains P.sets

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
