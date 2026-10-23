module

public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorIdx

@[expose] public section

/-!
# A monomial reads only the kept factors

Split out of `Compact.lean` (issue #62): used again by
`Theorems/CompactFactorsExact.lean` and by `ConPolyZono`'s own
`MonomialFactorIdxLeft`/`Right.lean`, both outside this file.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `a` – factor values
* `i` – generator index

## Hypotheses
* none

## Conclusion
* monomial over used factors equals the full monomial
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A monomial reads the kept factors and no others, which is the whole content
of dropping a factor. -/
theorem PolyZonotope.monomial_factorIdx {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) : -- --- CONCL ---
    PolyZonotope.monomial (fun k i => E (PolyZonotope.factorIdx E k) i)
        (fun k => a (PolyZonotope.factorIdx E k)) i
      = PolyZonotope.monomial E a i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  have h1 : (∏ k, a (PolyZonotope.factorIdx E k) ^ E (PolyZonotope.factorIdx E k) i)
      = ∏ k ∈ PolyZonotope.usedFactors E, a k ^ E k i := by
    rw [← Finset.prod_coe_sort (PolyZonotope.usedFactors E) fun k => a k ^ E k i]
    exact Equiv.prod_comp ((PolyZonotope.usedFactors E).orderIsoOfFin rfl).toEquiv
      fun x => a x ^ E x i
  have h2 : (∏ k ∈ PolyZonotope.usedFactors E, a k ^ E k i) = ∏ k, a k ^ E k i := by
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have hz : E k i = 0 := by
      by_contra hne
      exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, ⟨i, hne⟩⟩)
    rw [hz, pow_zero]
  rw [h1, h2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
