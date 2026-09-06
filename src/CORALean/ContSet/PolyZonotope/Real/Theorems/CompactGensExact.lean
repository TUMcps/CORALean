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

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.aux_sum_compactGens (PZ : PolyZonotope α) (a : Fin PZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i)
      = ∑ j : Fin PZ.compactGens.h,
          PolyZonotope.monomial PZ.compactGens.E a j • PZ.compactGens.G j := by
  rw [PolyZonotope.sum_monomial_merge PZ.E PZ.G a (PolyZonotope.rep PZ.E)
      (PolyZonotope.compactKeep PZ.E PZ.G) (PolyZonotope.col_rep PZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem PZ.E PZ.G hj,
    PolyZonotope.sum_compactKeep]
  rfl

-- so both inclusions hold at the very same coefficients
theorem PolyZonotope.compactGens_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compactGens.construct := by
  have key : ∀ (a : Fin PZ.p → ℝ) (β : Fin PZ.q → ℝ),
      PZ.c + (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i) + ∑ j, β j • PZ.GI j
        = PZ.c + (∑ j : Fin PZ.compactGens.h,
            PolyZonotope.monomial PZ.compactGens.E a j • PZ.compactGens.G j)
          + ∑ j, β j • PZ.GI j :=
    fun a _ => by rw [PolyZonotope.aux_sum_compactGens PZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, rfl⟩
    exact ⟨a, β, ha, hβ, (key a β).symm⟩

end CORALean.Real
