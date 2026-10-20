module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# `PolyZonotope.abs_monomial_le_one`

A monomial in factors of `[-1,1]` never leaves `[-1,1]` itself, which is what
lets every dependent generator be read as an independent one — the bound every
enclosing conversion out of this representation rests on.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `a` – factor values
* `i` – generator index

## Hypotheses
* `ha` – factor values are at most one

## Conclusion
* the monomial is at most one in absolute value
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A monomial never leaves `[-1,1]`, which is what lets every dependent
generator be read as an independent one. -/
theorem PolyZonotope.abs_monomial_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin p → ℝ} (ha : ∀ k, |a k| ≤ 1) (i : Fin h) :
    |PolyZonotope.monomial E a i| ≤ 1 := by
  rw [PolyZonotope.monomial, Finset.abs_prod]
  refine Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (ha k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
