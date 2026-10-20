module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Corners
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A box as its corners

## Inputs
* `I` – interval

## Hypotheses
* `hI` – lower end below upper end per coordinate

## Conclusion
* corner polytope is contained in the interval
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every corner of a nonempty box lies in the box, and the box is convex. -/
theorem Interval.contains_vPolytope (I : Interval (Vec ℝ n))
    (hI : ∀ j, I.inf j ≤ I.sup j) : -- --- CONCL ---
    I.vPolytope.construct ⊆ I.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ I.convex_construct
  rintro _ ⟨l, rfl⟩ j
  show I.inf j ≤ I.corner (signEquiv n l) j ∧ I.corner (signEquiv n l) j ≤ I.sup j
  unfold Interval.corner
  split_ifs
  · exact ⟨hI j, le_rfl⟩
  · exact ⟨le_rfl, hI j⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
