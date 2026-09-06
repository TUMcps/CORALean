import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The exponent matrix `plus` assembles

Split out of `Plus.lean` (issue #62): built again by `dependent` and `linComb`
in this directory, and by `ConPolyZono`'s own `plus`, `and` and `dependent`,
all outside this file.

Two exponent matrices side by side, block-diagonally: neither set's factors
reach the other's generators. Named so that its lemmas are stated at the plain
counts `Fin (p₁ + p₂)` rather than at a projection of `plus`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Two exponent matrices side by side, block-diagonally: neither set's factors
reach the other's generators. -/
def PolyZonotope.plusE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) : Fin (p₁ + p₂) → Fin (h₁ + h₂) → ℕ :=
  Fin.append (fun k => Fin.append (E₁ k) (fun _ => 0))
    (fun k => Fin.append (fun _ => 0) (E₂ k))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
