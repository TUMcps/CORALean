module

public import CORALean.Global.Cost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Theorems.RelaxWidthMultiCostMono
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti

@[expose] public section

/-!
# `PolyZonotope.relaxExpGreedyCost_mono`

Monotone in the round count.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The merge is monotone in the factor count and the kept and independent counts. -/
theorem PolyZonotope.aux_relaxExpMultiCost_mono {p p' d d' q q' : ℕ} (n : ℕ) (h : p ≤ p')
    (hd : d ≤ d') (hq : q ≤ q') :
    PolyZonotope.aux_relaxExpMultiCost n p d q ≤
      PolyZonotope.aux_relaxExpMultiCost n p' d' q' := by
  have := Cost.le_iff.mp (PolyZonotope.relaxWidthMultiCost_mono h)
  simp only [PolyZonotope.aux_relaxExpMultiCost, Cost.le_iff, Cost.ops_add] at this ⊢
  have g : n * (d + q + 3) + p * (d + 1) ≤ n * (d' + q' + 3) + p' * (d' + 1) := by gcongr
  omega


-- =======================================  MAIN THEOREM  ======================================= --

/-- Monotone in the round count. -/
theorem PolyZonotope.relaxExpGreedyCost_mono {N N' : ℕ} (n p h q : ℕ) (csel : Cost)
    (hN : N ≤ N') :
    PolyZonotope.relaxExpGreedyCost n p h q N csel ≤
      PolyZonotope.relaxExpGreedyCost n p h q N' csel := by
  have := Cost.le_iff.mp (PolyZonotope.aux_relaxExpMultiCost_mono n (le_refl p) (le_refl h)
    (Nat.add_le_add_left hN q))
  simp only [PolyZonotope.relaxExpGreedyCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
