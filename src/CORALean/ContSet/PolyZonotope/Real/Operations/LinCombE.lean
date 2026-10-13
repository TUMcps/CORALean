module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE

@[expose] public section

/-!
# The exponent matrix `linComb` assembles

Split out of `LinComb.lean` (issue #62): read again by the float layer's own
`linComb`, outside this file.

The two sets' factors block-diagonally as `plus` lays them out, repeated
across the two dependent blocks, and the fresh factor last, at exponent `1` on
the second block and `0` on the first.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exponent matrix of `linComb`: the two sets' factors block-diagonally as
`plus` lays them out, repeated across the two dependent blocks, and the fresh
factor last, at exponent `1` on the second block and `0` on the first. -/
def PolyZonotope.linCombE {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) :
    Fin (p₁ + p₂ + 1) → Fin (h₁ + h₂ + (h₁ + h₂ + 1)) → ℕ :=
  Fin.append
    (fun k => Fin.append (PolyZonotope.plusE E₁ E₂ k)
      (Fin.append (PolyZonotope.plusE E₁ E₂ k) (fun _ : Fin 1 => 0)))
    (fun _ : Fin 1 => Fin.append (fun _ => 0) (fun _ => 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
