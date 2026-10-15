module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.RelaxWidthGroupCostMono
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGroupCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpGroupCost_mono`

Monotone in the factor and merged counts.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the factor and merged counts. -/
theorem PolyZonotope.relaxExpGroupCost_mono {p p' k k' : ℕ} (n d : ℕ) (hp : p ≤ p')
    (hk : k ≤ k') :
    PolyZonotope.relaxExpGroupCost n p d k ≤
      PolyZonotope.relaxExpGroupCost n p' d k' := by -- --- PROOF ---
  have a := PolyZonotope.relaxWidthGroupCost_mono hp
  simp only [PolyZonotope.relaxExpGroupCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at a ⊢
  have e := Nat.mul_le_mul hk a
  have f : n * (k + 1) + d + k * n ≤ n * (k' + 1) + d + k' * n := by
    have := Nat.mul_le_mul_left n hk
    have := Nat.mul_le_mul_right n hk
    rw [Nat.mul_succ, Nat.mul_succ]
    omega
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
