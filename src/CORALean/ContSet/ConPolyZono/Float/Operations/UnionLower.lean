module

public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerA
public import CORALean.ContSet.ConPolyZono.Float.Operations.UnionLowerB
public import CORALean.ContSet.ConPolyZono.Real.Operations.UnionLowerR
public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# `ConPolyZono.unionLower` over a floating-point scalar

`Real.ConPolyZono.unionLower` at the stored floats: each operand's equations on its own factors,
shifted by the selector factor, with its own slacks (`unionLowerA`, `unionLowerR`,
`unionLowerB`). Halving and negating are exact, so the shift costs no slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {p₁ p₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Both operands' equations, switched by the selector factor, each row with its slack. -/
def ConPolyZono.unionLower (P₁ : PolyLevelSet 𝕋 p₁) (P₂ : PolyLevelSet 𝕋 p₂) :
    PolyLevelSet 𝕋 (p₁ + p₂ + 2) :=
  ⟨P₁.m + P₂.m, P₁.q + P₂.q + 1, ConPolyZono.unionLowerA P₁.A P₁.b P₂.A P₂.b,
    Real.ConPolyZono.unionLowerR P₁.R P₂.R, ConPolyZono.unionLowerB P₁.b P₂.b,
    ConPolyZono.plusB P₁.b_error P₂.b_error, fun _ => .eq⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
