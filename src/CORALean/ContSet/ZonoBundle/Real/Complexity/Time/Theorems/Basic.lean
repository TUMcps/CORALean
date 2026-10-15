module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Theorems.Basic
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ContSet/ZonoBundle/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ================================  `ZonoBundle.mapCost_mono`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the member count and in the generator bound, so bounds on the
operand's sizes give a bound on the cost. -/
theorem ZonoBundle.mapCost_mono {k k' h h' : ℕ} (cf : Cost) (hk : k ≤ k') (hh : h ≤ h') :
    ZonoBundle.mapCost cf k h ≤ ZonoBundle.mapCost cf k' h' :=
  Nat.mul_le_mul hk (Cost.le_iff.mp (Zonotope.mapCost_mono cf hh))


-- ===============================  `ZonoBundle.mtimesCost_mono`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the member count and in the generator bound, so bounds on the
operand's sizes give a bound on the cost. -/
theorem ZonoBundle.mtimesCost_mono {k k' h h' : ℕ} (m n : ℕ) (hk : k ≤ k') (hh : h ≤ h') :
    ZonoBundle.mtimesCost m n k h ≤ ZonoBundle.mtimesCost m n k' h' :=
  Nat.mul_le_mul hk (Cost.le_iff.mp (Zonotope.mtimesCost_mono m n hh))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
