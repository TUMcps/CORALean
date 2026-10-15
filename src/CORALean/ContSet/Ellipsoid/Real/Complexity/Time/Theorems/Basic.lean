module

public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.Global.Cost
public import CORALean.ContSet.Ellipsoid.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ===============================  `Ellipsoid.mtimesCost_mono`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the generator count, so a bound on the operand's size gives a
bound on the cost. -/
theorem Ellipsoid.mtimesCost_mono {k k' : ℕ} (m n : ℕ) (hle : k ≤ k') :
    Ellipsoid.mtimesCost m n k ≤ Ellipsoid.mtimesCost m n k' :=
  Nat.mul_le_mul_right _ (Nat.succ_le_succ hle)


-- ================================  `Ellipsoid.plusCost_mono`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both generator counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem Ellipsoid.plusCost_mono {q₁ q₁' q₂ q₂' : ℕ} (n : ℕ) (h1 : q₁ ≤ q₁') (h2 : q₂ ≤ q₂') :
    Ellipsoid.plusCost n q₁ q₂ ≤ Ellipsoid.plusCost n q₁' q₂' :=
  Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
