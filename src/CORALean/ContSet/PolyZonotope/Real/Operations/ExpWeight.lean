module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

@[expose] public section

/-!
# `PolyZonotope.expWeight`

The weight of an edge `i → j` of `[1, Def. 5]`, summed over every factor so that the agreeing
ones contribute nothing: at an edge the columns differ at one index, so it is the single `eDiff`
of the definition. Over a bare exponent matrix, as the edges are.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `i` – first generator index
* `j` – second generator index

## Output
* total exponent difference of the two generators

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications in
      Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An edge's weight, summed over every factor. -/
def PolyZonotope.expWeight {p h : ℕ} (E : Fin p → Fin h → ℕ) (i j : Fin h) : ℕ :=
  ∑ k, PolyZonotope.eDiff (E k i) (E k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
