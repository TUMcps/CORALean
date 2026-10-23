module

public import CORALean.ContSet.ConPolyZono.Real.Operations.CompactGens
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.FiberSumEqZeroOfNotMem
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumCompactKeep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumMonomialMerge

@[expose] public section

/-!
# Merging equal generator exponent columns loses nothing

The result is [1, Prop. 1].

`compactGens` leaves the whole constraint block alone, so membership in `cons` transfers by
definition and only the generator sum moves. An equality of sets with no hypothesis, which is what
makes this stage bookkeeping. The `key` is stated with the *original* center and independent block
on both sides, keeping the equation to the one sum that changes.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is unchanged

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem ConPolyZono.aux_sum_compactGens (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i)
      = ∑ j : Fin cPZ.compactGens.h,
          PolyZonotope.monomial cPZ.compactGens.E a j • cPZ.compactGens.G j := by -- --- PROOF ---
  rw [PolyZonotope.sum_monomial_merge cPZ.E cPZ.G a (PolyZonotope.rep cPZ.E)
      (PolyZonotope.compactKeep cPZ.E cPZ.G) (PolyZonotope.col_rep cPZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem cPZ.E cPZ.G hj,
    PolyZonotope.sum_compactKeep]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

-- the constraint block is copied, so one factor vector answers for both sides
theorem ConPolyZono.compactGens_exact (cPZ : ConPolyZono α) : -- --- CONCL ---
    cPZ.construct = cPZ.compactGens.construct := by -- --- PROOF ---
  have key : ∀ (a : Fin cPZ.p → ℝ) (β : Fin cPZ.qI → ℝ),
      cPZ.c + (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i) + ∑ j, β j • cPZ.GI j
        = cPZ.c + (∑ j : Fin cPZ.compactGens.h,
            PolyZonotope.monomial cPZ.compactGens.E a j • cPZ.compactGens.G j)
          + ∑ j, β j • cPZ.GI j :=
    fun a _ => by rw [ConPolyZono.aux_sum_compactGens cPZ a]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, β, hβ, hsat, rfl⟩
    exact ⟨a, β, hβ, hsat, key a β⟩
  · rintro _ ⟨a, β, hβ, hsat, rfl⟩
    exact ⟨a, β, hβ, hsat, (key a β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
