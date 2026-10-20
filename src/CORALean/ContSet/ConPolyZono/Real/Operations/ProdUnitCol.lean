module

public import CORALean.ContSet.ConPolyZono.Real.Operations.UnitCol

@[expose] public section

/-!
# The monomial of a one-factor column

What `unitCol i e` names: `a i ^ e`, every other factor dropping out at exponent
zero. `PolyZonotope.monomial_identE` is this at `e = 1` for a whole matrix.

## Inputs
* `p` – number of factors
* `a` – factor values
* `i` – factor index
* `e` – exponent

## Hypotheses
* none

## Conclusion
* the monomial is that factor to the exponent
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.prod_unitCol {p : ℕ} (a : Fin p → ℝ) (i : Fin p) (e : ℕ) : -- --- CONCL ---
    (∏ k, a k ^ ConPolyZono.unitCol i e k) = a i ^ e := by -- --- PROOF ---
  rw [Finset.prod_eq_single i]
  · rw [ConPolyZono.unitCol, if_pos rfl]
  -- every other factor sits at exponent zero
  · intro k _ hk
    rw [ConPolyZono.unitCol, if_neg hk, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
