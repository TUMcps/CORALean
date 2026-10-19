module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Compact
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCongr
public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

@[expose] public section

/-!
# `PolyLevelSet.compact` is exact

Merging monomials with one exponent column adds their coefficient columns, which leaves
`A μ_R(x)` alone at every point, and a dropped column is zero: `sum_monomial_merge` with the
coefficient columns as generators. The rows read the same, so the set is the same.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `A v` as the sum of the coefficient columns weighted by `v`. -/
theorem PolyLevelSet.aux_mulVec_eq_sum {m q : ℕ} (A : Mat ℝ m q) (v : Vec ℝ q) :
    A *ᵥ v = ∑ l, v l • (fun i => A i l) := by
  funext i
  show (∑ l, A i l * v l) = (∑ l, v l • (fun i => A i l)) i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _


-- =======================================  MAIN THEOREM  ======================================= --

/-- The merged monomials denote the same set. -/
theorem PolyLevelSet.compact_exact (P : PolyLevelSet n) :
    P.compact.construct = P.construct := by -- --- PROOF ---
  ext x
  refine PolyLevelSet.mem_congr P ?_
  rw [PolyLevelSet.aux_mulVec_eq_sum, PolyLevelSet.aux_mulVec_eq_sum,
    PolyZonotope.sum_monomial_merge P.R (fun l i => P.A i l) x (PolyZonotope.rep P.R)
      (PolyZonotope.compactKeep P.R (fun l i => P.A i l)) (PolyZonotope.col_rep P.R)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem P.R (fun l i => P.A i l) hj,
    PolyZonotope.sum_compactKeep]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
