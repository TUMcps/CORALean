module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Corners

@[expose] public section

/-!
# A box as its corners — the construction

`Interval.corner` and `Interval.vPolytope` are the constructions; `Interval_to_VPolytope` states and
proves what they guarantee.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The corner that takes each coordinate's upper end where `σ` says so. -/
def Interval.corner (I : Interval (Vec ℝ n)) (σ : Fin n → Bool) : Vec ℝ n :=
  fun j => if σ j then I.sup j else I.inf j

noncomputable def Interval.vPolytope (I : Interval (Vec ℝ n)) : VPolytope (Vec ℝ n) where
  k := 2 ^ n
  V := fun l => I.corner (signEquiv n l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
