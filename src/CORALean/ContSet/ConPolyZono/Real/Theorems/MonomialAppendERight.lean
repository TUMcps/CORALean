import CORALean.ContSet.ConPolyZono.Real.Operations.AppendE

/-!
# `ConPolyZono.monomial_appendE_right`

A monomial read back off `appendE`'s right half is the monomial of the
original right exponent matrix — the factors being shared, `appendE` only
reshapes which columns index them.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_appendE_right {p s t : ℕ} (E₁ : Fin p → Fin s → ℕ)
    (E₂ : Fin p → Fin t → ℕ) (a : Fin p → ℝ) (l : Fin t) :
    PolyZonotope.monomial (ConPolyZono.appendE E₁ E₂) a (Fin.natAdd s l)
      = PolyZonotope.monomial E₂ a l := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [ConPolyZono.appendE, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
