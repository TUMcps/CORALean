module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.ReduceGirardCost

@[expose] public section

/-!
# `PolyZonotope.reduceGirardCost_mono`

Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem PolyZonotope.reduceGirardCost_mono {h h' q q' : ℕ} (n : ℕ) (hh : h ≤ h') (hq : q ≤ q') :
    PolyZonotope.reduceGirardCost n h q
      ≤ PolyZonotope.reduceGirardCost n h' q' := by -- --- PROOF ---
  -- the joint width is what every term but the last is stated in
  have hs : h + q ≤ h' + q' := Nat.add_le_add hh hq
  refine Cost.add_le_add (Cost.add_le_add ?_ ?_) (PolyZonotope.reduceByCost_mono n hh hq)
  · exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hs) hs) le_rfl
  · exact Nat.mul_le_mul_left _ (Cost.sort_mono hs)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
