module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.Global.Corners
public import CORALean.ContSet.Interval.Real.Operations.Vertices

@[expose] public section

/-!
# A box as its corners

The vectors' corners (`vPolytope`), and for an interval matrix CORA's `matPolytope`, which builds
the vertex list of `Interval.vertices`.

## Inputs
* `I` – interval
* `σ` – upper end per coordinate

## Output
* corner taking the upper end where `σ` says so
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

/-- The hull of a box's `2ⁿ` corners. -/
noncomputable def Interval.vPolytope (I : Interval (Vec ℝ n)) : VPolytope (Vec ℝ n) where
  k := 2 ^ n
  V := fun l => I.corner (signEquiv n l)

/-- CORA's `intervalMatrix/matPolytope`: the vertices of the interval matrix, as a matrix polytope.
They are listed once each (`unique` in CORA), in an arbitrary order. -/
noncomputable def Interval.matPolytope {m p : ℕ} (A : Interval (Mat ℝ m p)) :
    VPolytope (Mat ℝ m p) where
  k := A.vertices.card
  V := fun l => (A.vertices.equivFin.symm l : Mat ℝ m p)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
