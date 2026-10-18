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


-- =================================  `HPolytope.IsSlackFree`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Both slacks read `0`: every inequality is read at its stored `b`, every equality exactly. -/
def HPolytope.IsSlackFree (P : HPolytope 𝕋 (Vec 𝕋 n)) : Prop :=
  (∀ i, toReal (P.b_error i) = 0) ∧ ∀ i, toReal (P.be_error i) = 0


-- ===================================  `HPolytope.ErrFree`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---

/-- The box is the origin and the polytope is slack-free: it denotes its stored rows exactly. -/
def HPolytope.ErrFree (P : HPolytope 𝕋 (Vec 𝕋 n)) : Prop :=
  (∀ j, toReal (P.I_error.inf j) = 0 ∧ toReal (P.I_error.sup j) = 0) ∧ P.IsSlackFree

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
