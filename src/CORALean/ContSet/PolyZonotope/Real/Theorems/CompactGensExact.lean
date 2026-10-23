module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Col
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactGens
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx
public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import CORALean.ContSet.PolyZonotope.Real.Theorems.FiberSumEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumCompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumMonomialMerge

@[expose] public section

/-!
# Merging equal exponent columns loses nothing

`compactGens` touches neither `p` nor `q`, so one factor vector reads both sides
and both inclusions come out of the single equation below. An equality of sets
with no hypothesis anywhere, which is what makes this bookkeeping.

The `key` is stated with the *original* center and independent block on both
sides. They are the compacted ones up to unfolding, and writing them so keeps
the equation to the one sum that actually changes.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* merging equal columns leaves the set unchanged
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.aux_sum_compactGens (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : -- --- CONCL ---
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
theorem PolyZonotope.compactGens_exact (pZ : PolyZonotope α) : -- --- CONCL ---
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
