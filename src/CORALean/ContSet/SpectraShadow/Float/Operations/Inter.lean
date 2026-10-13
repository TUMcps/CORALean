module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Absorb
public import CORALean.ContSet.SpectraShadow.Float.Operations.TieInter

@[expose] public section

/-!
# `SpectraShadow.inter`

CORA's `@spectraShadow/and_`, `'exact'` branch, over a floating-point scalar: each shadow's
error box absorbed into its inequality (`absorb`), then the two tied to one point
(`tieInter`). Nothing is computed: every stored entry is a stored float, its exact negation,
`zero` or `one`. Stated as an enclosure only; the error box of the result is the origin.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.inter (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let T₁ := S₁.absorb
  let T₂ := S₂.absorb
  T₁.tieInter T₂

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
