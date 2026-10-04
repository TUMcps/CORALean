import Mathlib.Algebra.Group.Pointwise.Set.Basic
import CORALean.ContSet.Polygon.Real.Operations.Minus
import CORALean.ContSet.Polygon.Real.Theorems.PlusExact
import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint

/-!
# `Polygon.minus` is the translate

Exactly: the polygon, every point moved by `-p`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open Pointwise in
theorem Polygon.minus_exact (P : Polygon) (p : Vec ℝ 2) :
    (fun x => x - p) '' ContSet.construct P = ContSet.construct (P.minus p) := by -- --- PROOF ---
  -- the singleton `{-p}` is what `OfPoint` denotes
  have hQ : ContSet.construct (OfPoint.ofPoint (-p) : Polygon) = {-p} := by
    ext x
    show x ∈ SetUnion.construct _ ↔ _
    simp only [SetUnion.construct, OfPoint.ofPoint, List.mem_singleton, Set.iUnion_iUnion_eq_left]
    change x ∈ (VPolytope.point (-p)).construct ↔ _
    rw [VPolytope.construct_point]
  have h := Polygon.plus_exact P (OfPoint.ofPoint (-p))
  rw [hQ, Set.add_singleton] at h
  -- the translate, written as the sum with `{-p}`
  have : (fun x : Vec ℝ 2 => x - p) = fun x => x + -p := by funext x; simp [sub_eq_add_neg]
  rw [this, h]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
