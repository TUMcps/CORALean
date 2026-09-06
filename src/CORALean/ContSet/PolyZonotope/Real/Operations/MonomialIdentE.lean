import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# The monomial `identE` produces is the factor itself

Split out of `IdentE.lean` (issue #62): read again by `Theorems/
DependentExact.lean` at both layers and by two `Conversion/` files, all
outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

theorem PolyZonotope.monomial_identE {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    PolyZonotope.monomial (PolyZonotope.identE m) a i = a i := by
  rw [PolyZonotope.monomial, Finset.prod_eq_single i]
  · have h1 : PolyZonotope.identE m i i = 1 := if_pos rfl
    rw [h1, pow_one]
  -- every other factor sits at exponent zero
  · intro k _ hk
    have h0 : PolyZonotope.identE m k i = 0 := if_neg hk
    rw [h0, pow_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Real
