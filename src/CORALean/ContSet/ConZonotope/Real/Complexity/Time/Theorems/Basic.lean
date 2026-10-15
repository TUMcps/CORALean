module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection
public import CORALean.Global.Cost
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.IntersectionCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Map
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.ConZonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.MtimesIntervalMatCostMono
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.MtimesIntervalMatCost
public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.ReduceGirardCostMono
public import CORALean.ContSet.ConZonotope.Real.Complexity.Time.Operations.ReduceCost

@[expose] public section

/-!
# `ContSet/ConZonotope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ===========================  `ConZonotope.intersectionCost_mono`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the second operand's generator count, so a bound on its size
gives a bound on the cost. -/
theorem ConZonotope.intersectionCost_mono {h₂ h₂' : ℕ} (n : ℕ) (hh : h₂ ≤ h₂') :
    ConZonotope.intersectionCost n h₂ ≤ ConZonotope.intersectionCost n h₂' :=
  Nat.mul_le_mul_left _ (Nat.succ_le_succ hh)


-- ================================  `ConZonotope.mapCost_mono`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mapCost_mono {h h' : ℕ} (cf : Cost) (hh : h ≤ h') :
    ConZonotope.mapCost cf h ≤ ConZonotope.mapCost cf h' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hh)


-- ==============================  `ConZonotope.mtimesCost_mono`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    ConZonotope.mtimesCost m n h ≤ ConZonotope.mtimesCost m n h' :=
  ConZonotope.mapCost_mono _ hh


-- =========================  `ConZonotope.mtimesIntervalMatCost_mono`  ========================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.mtimesIntervalMatCost_mono {h h' : ℕ} (m n : ℕ) (hh : h ≤ h') :
    ConZonotope.mtimesIntervalMatCost m n h ≤ ConZonotope.mtimesIntervalMatCost m n h' :=
  Zonotope.mtimesIntervalMatCost_mono m n hh


-- ==============================  `ConZonotope.reduceCost_mono`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem ConZonotope.reduceCost_mono {h h' : ℕ} (n : ℕ) (hh : h ≤ h') :
    ConZonotope.reduceCost n h ≤ ConZonotope.reduceCost n h' :=
  Zonotope.reduceGirardCost_mono n hh

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
