module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# `ContSet/HPolytope/Float/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===================================  `HPolytope.ErrFree`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)

/-- The error box is the origin, as every real number it stores reads: the polytope denotes its
nominal part. What every constructor returns, and what `absorb` returns. -/
def HPolytope.ErrFree (P : HPolytope 𝕋 (Vec 𝕋 n)) : Prop :=
  ∀ j, toReal (P.I_error.inf j) = 0 ∧ toReal (P.I_error.sup j) = 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
