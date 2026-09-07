import CORALean.ContSet.PolyZonotope.Real.Operations.Col
import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactGens
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Real.Operations.Rep
import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

/-!
# Merging equal exponent columns loses nothing

`compactGens` touches neither `p` nor `q`, so one factor vector reads both sides
and both inclusions come out of the single equation below. An equality of sets
with no hypothesis anywhere, which is what makes this bookkeeping.

The `key` is stated with the *original* centre and independent block on both
sides. They are the compacted ones up to unfolding, and writing them so keeps
the equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.aux_sum_compactGens (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ j : Fin pZ.compactGens.h,
          PolyZonotope.monomial pZ.compactGens.E a j • pZ.compactGens.G j := by -- --- PROOF ---
  rw [PolyZonotope.sum_monomial_merge pZ.E pZ.G a (PolyZonotope.rep pZ.E)
      (PolyZonotope.compactKeep pZ.E pZ.G) (PolyZonotope.col_rep pZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem pZ.E pZ.G hj,
    PolyZonotope.sum_compactKeep]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

-- so both inclusions hold at the very same coefficients
theorem PolyZonotope.compactGens_exact (pZ : PolyZonotope α) :
    pZ.construct = pZ.compactGens.construct := by -- --- PROOF ---
  have key : ∀ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ),
      pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, β j • pZ.GI j
        = pZ.c + (∑ j : Fin pZ.compactGens.h,
            PolyZonotope.monomial pZ.compactGens.E a j • pZ.compactGens.G j)
          + ∑ j, β j • pZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactGens pZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (key a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
