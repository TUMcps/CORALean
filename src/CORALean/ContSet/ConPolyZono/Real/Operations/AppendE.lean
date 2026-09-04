import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.appendE`

Two exponent matrices over the *same* factors, side by side, which is what an
intersection has to do. Not `PolyZonotope.plusE`, which puts two *factor* sets
side by side and would decouple the very columns this couples.

`Theorems/MonomialAppendELeft` and `Theorems/MonomialAppendERight` read a
monomial back off each half of the append.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

def ConPolyZono.appendE {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ) (E₂ : Fin p → Fin t → ℕ) :
    Fin p → Fin (s + t) → ℕ :=
  fun k => Fin.append (E₁ k) (E₂ k)

end CORALean.Real
