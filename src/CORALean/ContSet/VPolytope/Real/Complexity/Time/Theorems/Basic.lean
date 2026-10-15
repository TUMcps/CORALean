module

public import CORALean.ContSet.VPolytope.Real.Operations.Mtimes
public import CORALean.Global.Cost
public import CORALean.ContSet.VPolytope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.VPolytope.Real.Operations.Plus
public import CORALean.ContSet.VPolytope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `ContSet/VPolytope/Real/Complexity/Time/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real


-- ===============================  `VPolytope.mtimesCost_mono`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in the vertex count, so a bound on the operand's size gives a
bound on the cost. -/
theorem VPolytope.mtimesCost_mono {k k' : ℕ} (m n : ℕ) (hle : k ≤ k') :
    VPolytope.mtimesCost m n k ≤ VPolytope.mtimesCost m n k' :=
  Nat.mul_le_mul_right _ hle


-- ================================  `VPolytope.plusCost_mono`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Monotone in both vertex counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem VPolytope.plusCost_mono {k₁ k₁' k₂ k₂' : ℕ} (n : ℕ) (h1 : k₁ ≤ k₁') (h2 : k₂ ≤ k₂') :
    VPolytope.plusCost n k₁ k₂ ≤ VPolytope.plusCost n k₁' k₂' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
