module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import CORALean.ContSet.Polygon.Real.Operations.Minus
public import CORALean.ContSet.Polygon.Real.Theorems.PlusExact
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructPoint

@[expose] public section

/-!
# `Polygon.minus` is the translate

Exactly: the polygon, every point moved by `-p`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open Pointwise in
theorem Polygon.minus_exact (P : Polygon) (p : Vec ℝ 2) : -- --- CONCL ---
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
