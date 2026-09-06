import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens
import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMem
import CORALean.ContSet.PolyZonotope.Real.Operations.SumCompactKeep
import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

/-!
# Merging equal generator exponent columns loses nothing

`compactGens` leaves the whole constraint block alone, so `satisfies` transfers
by definition and only the generator sum moves. An equality of sets with no
hypothesis, which is what makes this stage bookkeeping.

The `key` is stated with the *original* centre and independent block on both
sides. They are the compacted ones up to unfolding, and writing them so keeps
the equation to the one sum that actually changes.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem ConPolyZono.aux_sum_compactGens (C : ConPolyZono α) (a : Fin C.p → ℝ) :
    (∑ i, PolyZonotope.monomial C.E a i • C.G i)
      = ∑ j : Fin C.compactGens.h,
          PolyZonotope.monomial C.compactGens.E a j • C.compactGens.G j := by
  rw [PolyZonotope.sum_monomial_merge C.E C.G a (PolyZonotope.rep C.E)
      (PolyZonotope.compactKeep C.E C.G) (PolyZonotope.col_rep C.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem C.E C.G hj,
    PolyZonotope.sum_compactKeep]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

-- the constraint block is copied, so one factor vector answers for both sides
theorem ConPolyZono.compactGens_exact (C : ConPolyZono α) :
    C.construct = C.compactGens.construct := by
  have key : ∀ (a : Fin C.p → ℝ) (β : Fin C.q → ℝ),
      C.c + (∑ i, PolyZonotope.monomial C.E a i • C.G i) + ∑ j, β j • C.GI j
        = C.c + (∑ j : Fin C.compactGens.h,
            PolyZonotope.monomial C.compactGens.E a j • C.compactGens.G j)
          + ∑ j, β j • C.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactGens C a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, key a β⟩
  · rintro _ ⟨a, β, ha, hβ, hsat, rfl⟩
    exact ⟨a, β, ha, hβ, hsat, (key a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
