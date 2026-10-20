module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.appendE`

Two exponent matrices over the *same* factors, side by side, which is what an
intersection has to do. Not `PolyZonotope.plusE`, which puts two *factor* sets
side by side and would decouple the very columns this couples.

`Theorems/MonomialAppendELeft` and `Theorems/MonomialAppendERight` read a
monomial back off each half of the append.

## Inputs
* `p` – number of factors
* `q` – columns of first matrix
* `t` – columns of second matrix
* `E₁` – first exponent matrix
* `E₂` – second exponent matrix

## Output
* the two exponent matrices side by side
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.appendE {p q t : ℕ} (E₁ : Fin p → Fin q → ℕ) (E₂ : Fin p → Fin t → ℕ) :
    Fin p → Fin (q + t) → ℕ :=
  fun k => Fin.append (E₁ k) (E₂ k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
