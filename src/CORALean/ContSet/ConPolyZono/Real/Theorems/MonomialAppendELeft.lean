import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.monomial_appendE_left`

A monomial read back off `appendE`'s left half is the monomial of the original
left exponent matrix — the factors being shared, `appendE` only reshapes which
columns index them.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_appendE_left {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin s) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.castAdd t l)
      = PolyZonotope.monomial E₁ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_left]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
