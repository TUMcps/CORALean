module

public import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

@[expose] public section

/-!
# `ConPolyZono.monomial_appendE_left`

A monomial read back off `appendE`'s left half is the monomial of the original
left exponent matrix — the factors being shared, `appendE` only reshapes which
columns index them.

## Inputs
* `p` – number of factors
* `q` – columns of first matrix
* `t` – columns of second matrix
* `E₁` – first exponent matrix
* `E₂` – second exponent matrix
* `a` – factor values
* `l` – column index

## Hypotheses
* none

## Conclusion
* the left columns of the joined matrix give the first matrix's monomials
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_appendE_left {p q t : ℕ} (E₁ : Fin p → Fin q → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin q) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.castAdd t l)
      = PolyZonotope.monomial E₁ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_left]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
