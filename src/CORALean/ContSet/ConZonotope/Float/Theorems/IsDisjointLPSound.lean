module

public import CORALean.ContSet.ConZonotope.Float.Operations.IsDisjointLP
public import CORALean.ContSet.ConZonotope.Float.Theorems.SeparatesAlongSound

@[expose] public section

/-!
# `ConZonotope.isDisjointLP` is sound when `true`

A direction along which the first set's upper bound lies strictly below the
second's lower bound leaves no point for both, whichever direction it is. So
the verdict is sound for every direction the simplex could have proposed; only
its completeness depends on the simplex, and none is claimed.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* `h` – the test answers true

## Conclusion
* the two sets are disjoint
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.isDisjointLP_sound {cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (h : cZ₁.isDisjointLP cZ₂ = true) : Disjoint cZ₁.construct cZ₂.construct := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact ConZonotope.separatesAlong_sound h
  · exact ConZonotope.separatesAlong_sound h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
