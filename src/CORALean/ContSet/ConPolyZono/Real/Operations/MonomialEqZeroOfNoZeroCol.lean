module

public import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

@[expose] public section

/-!
# A column with no constant term vanishes at zero factors

The one thing `NoZeroCol` is for. A degree-`0` column would evaluate to `1` here
instead, and that is exactly the gap in [1, Thm. 1] this formalization closes by
hypothesis: the union's branch that pins one operand's factors to `0` expects
that operand's whole block to drop out.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_eq_zero_of_noZeroCol {p h : ℕ} {E : Fin p → Fin h → ℕ}
    (hE : ConPolyZono.NoZeroCol E) {a : Fin p → ℝ} (ha : ∀ k, a k = 0) (i : Fin h) :
    PolyZonotope.monomial E a i = 0 := by
  obtain ⟨k, hk⟩ := hE i
  rw [PolyZonotope.monomial]
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  rw [ha k, zero_pow hk]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
