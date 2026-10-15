module

public import CORALean.ContSet.Capsule.Real.Operations.ConvHull
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.RadiusCost
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.ConvHullCost
public import CORALean.ContSet.Capsule.Real.Operations.Enclose
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Theorems.MtimesCostMono
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.EncloseCost
public import CORALean.ContSet.Capsule.Real.Operations.EnclosePoints
public import CORALean.Global.Cost
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.EnclosePointsCost
public import CORALean.ContSet.Capsule.Real.Operations.Plus
public import CORALean.ContSet.Capsule.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ContSet/Capsule/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ===============================  `Capsule.convHullCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the dimension. -/
theorem Capsule.convHullCost_mono {n n' : ℕ} (h : n ≤ n') :
    Capsule.convHullCost n ≤ Capsule.convHullCost n' := by
  simp only [Capsule.convHullCost, Capsule.radiusCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  omega


-- ================================  `Capsule.encloseCost_mono`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both dimensions. -/
theorem Capsule.encloseCost_mono {n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    Capsule.encloseCost n m ≤ Capsule.encloseCost n' m' :=
  Cost.add_le_add (Capsule.mtimesCost_mono hn hm) (Capsule.convHullCost_mono hn)


-- =============================  `Capsule.enclosePointsCost_mono`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both. -/
theorem Capsule.enclosePointsCost_mono {n n' N N' : ℕ} (hn : n ≤ n') (hN : N ≤ N') :
    Capsule.enclosePointsCost n N ≤ Capsule.enclosePointsCost n' N' :=
  Nat.add_le_add (Nat.mul_le_mul hN (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)) hn


-- =================================  `Capsule.plusCost_mono`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the dimension. -/
theorem Capsule.plusCost_mono {n n' : ℕ} (h : n ≤ n') : Capsule.plusCost n ≤ Capsule.plusCost n' :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
