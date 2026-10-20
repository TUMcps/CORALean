module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A monomial splits along a set of factors

`∏ₖ aₖ^{E k i}` is the product over all factors with the exponents in `V` zeroed, times the product
over `V`: what `partZonotope` and `subs` do to a generator's monomial.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `V` – selected factors
* `a` – factor values
* `i` – generator index

## Hypotheses
* none

## Conclusion
* the monomial splits into the part off and the part on the selected factors
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A monomial is the product of its part outside `V` and its part in `V`. -/
theorem PolyZonotope.monomial_split {p h : ℕ} (E : Fin p → Fin h → ℕ) (V : Finset (Fin p))
    (a : Fin p → ℝ) (i : Fin h) : -- --- CONCL ---
    PolyZonotope.monomial E a i
      = (∏ k, a k ^ (if k ∈ V then 0 else E k i)) * ∏ k ∈ V, a k ^ E k i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  rw [← Finset.prod_mul_prod_compl V (fun k => a k ^ E k i)]
  rw [mul_comm]
  congr 1
  -- the part outside `V`: the masked product agrees there, and is `1` on `V`
  rw [← Finset.prod_mul_prod_compl V]
  have h1 : ∏ k ∈ V, a k ^ (if k ∈ V then 0 else E k i) = 1 :=
    Finset.prod_eq_one fun k hk => by simp [hk]
  rw [h1, one_mul]
  exact Finset.prod_congr rfl fun k hk => by simp [Finset.mem_compl.mp hk]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
