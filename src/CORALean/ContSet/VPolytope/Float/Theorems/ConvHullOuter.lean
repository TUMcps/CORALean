module

public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.VPolytope.Float.Operations.ConvHull
public import CORALean.ContSet.VPolytope.Float.Theorems.NominalEq
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvHullExact

@[expose] public section

/-!
# `VPolytope.convHull` contains the convex hull of the two operands

The convex hull of the union of the two stored sets sits inside the stored hull. A point of an
operand is its nominal part plus its error: the first is a vertex combination of the joined list,
the second is in the hull of the two boxes; and the joined set, a sum of two convex sets, is
convex. Not exact, since the box is a hull of boxes and every nominal vertex is carried as stored.

## Inputs
* `P` – first polytope
* `Q` – second polytope

## Hypotheses
* none

## Conclusion
* the convex hull of both operands lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The joined list's nominal part is the real hull of the two nominal parts. -/
theorem VPolytope.aux_convHull_nominal (P Q : VPolytope (Vec 𝕋 n)) : -- --- CONCL ---
    nominalSet (P.convHull Q) = convexHull ℝ (nominalSet P ∪ nominalSet Q) := by -- --- PROOF ---
  have h : nominal (P.convHull Q) = (nominal P).convHull (nominal Q) := by
    rw [VPolytope.nominal_eq, VPolytope.nominal_eq, VPolytope.nominal_eq]
    unfold Real.VPolytope.convHull VPolytope.convHull
    congr 1
    funext l
    refine Fin.addCases (fun j => ?_) (fun j => ?_) l <;> simp
  show Real.VPolytope.construct (nominal (P.convHull Q)) =
    convexHull ℝ (Real.VPolytope.construct (nominal P) ∪ Real.VPolytope.construct (nominal Q))
  rw [h]
  exact Real.VPolytope.convHull_exact _ _


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.convHull_outer (P Q : VPolytope (Vec 𝕋 n)) : -- --- CONCL ---
    convexHull ℝ (P.construct ∪ Q.construct) ⊆ (P.convHull Q).construct := by -- --- PROOF ---
  have hbox : (I_error (P.convHull Q)).construct = (P.I_error.or Q.I_error).construct := rfl
  refine convexHull_min ?_ ?_
  · -- each operand's point is a nominal point plus an error
    rintro x (⟨a, ha, e, he, rfl⟩ | ⟨a, ha, e, he, rfl⟩)
    · refine ⟨a, ?_, e, ?_, rfl⟩
      · rw [VPolytope.aux_convHull_nominal]
        exact subset_convexHull ℝ _ (Or.inl ha)
      · exact Interval.or_outer P.I_error Q.I_error (Or.inl he)
    · refine ⟨a, ?_, e, ?_, rfl⟩
      · rw [VPolytope.aux_convHull_nominal]
        exact subset_convexHull ℝ _ (Or.inr ha)
      · exact Interval.or_outer P.I_error Q.I_error (Or.inr he)
  · -- a sum of two convex sets
    refine Convex.add ?_ ?_
    · rw [VPolytope.aux_convHull_nominal]
      exact convex_convexHull ℝ _
    · exact Real.Interval.convex_construct _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
