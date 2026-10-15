module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.DependentCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.Global.Cost
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.IntersectionCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MtimesCost

@[expose] public section

/-!
# `ContSet/ConPolyZono/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ===========================  `ConPolyZono.intersectionCost_mono`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the second operand's dependent-generator count, so a bound on
its size gives a bound on the cost. -/
theorem ConPolyZono.intersectionCost_mono {h₂ h₂' : ℕ} (n : ℕ) (hh : h₂ ≤ h₂') :
    ConPolyZono.intersectionCost n h₂ ≤ ConPolyZono.intersectionCost n h₂' :=
  Cost.add_le_add le_rfl (Cost.add_le_add (Nat.mul_le_mul_left _ hh) le_rfl)


-- ================================  `ConPolyZono.mapCost_mono`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.mapCost_mono {h h' qI q' : ℕ} (cf : Cost) (hh : h ≤ h') (hq : qI ≤ q') :
    ConPolyZono.mapCost cf h qI ≤ ConPolyZono.mapCost cf h' q' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.add_le_add hh hq))


-- ==============================  `ConPolyZono.mtimesCost_mono`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts, so bounds on the operand's sizes give a
bound on the cost. -/
theorem ConPolyZono.mtimesCost_mono {h h' qI q' : ℕ} (k n : ℕ) (hh : h ≤ h') (hq : qI ≤ q') :
    ConPolyZono.mtimesCost k n h qI ≤ ConPolyZono.mtimesCost k n h' q' :=
  ConPolyZono.mapCost_mono _ hh hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
