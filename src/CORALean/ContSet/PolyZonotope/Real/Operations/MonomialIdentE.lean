module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

@[expose] public section

/-!
# The monomial `identE` produces is the factor itself

Split out of `IdentE.lean` (issue #62): read again by `Theorems/
DependentExact.lean` at both layers and by two `Conversion/` files, all
outside this file.

## Inputs
* `m` – size
* `a` – factor values
* `i` – generator index

## Hypotheses
* none

## Conclusion
* the monomial equals the factor value itself
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.monomial_identE {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : -- --- CONCL ---
    PolyZonotope.monomial (PolyZonotope.identE m) a i = a i := by -- --- PROOF ---
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
