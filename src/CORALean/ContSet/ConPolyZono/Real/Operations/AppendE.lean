import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.appendE`

Two exponent matrices over the *same* factors, side by side, which is what an
intersection has to do. Not `PolyZonotope.plusE`, which puts two *factor* sets
side by side and would decouple the very columns this couples.

The two lemmas read a monomial back off each half of the append, the factors
being shared. They are three lines each and say nothing except what the
definition is for, so they stay with it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

def ConPolyZono.appendE {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ) (E₂ : Fin p → Fin t → ℕ) :
    Fin p → Fin (s + t) → ℕ :=
  fun k => Fin.append (E₁ k) (E₂ k)

theorem ConPolyZono.monomial_appendE_left {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.castAdd t l)
      = PolyZonotope.monomial E₁ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_left]

theorem ConPolyZono.monomial_appendE_right {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin t) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.natAdd s l)
      = PolyZonotope.monomial E₂ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_right]

end CORALean.Real
