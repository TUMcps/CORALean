module

public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# `Zonotope.plusBox`

A box that holds everything `plus` may contain beyond the Minkowski sum of its operands.

Only the center is rounded: `plus` joins the generators of both operands without changing them.
So the box adds up two parts.

* A bound on the rounding error of the new center, computed in `𝕋` with directed rounding. It
  uses that `addDown` never exceeds the exact sum, and that `subDown` against `addUp` never
  exceeds the gap below it.
* The error box of the result.

It is not a reduction: no class asks a representation how far a binary operation may stray from
its inputs, and only the definition of `plus` can say.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box holding the rounding errors of `Z₁.plus Z₂`: the center's rounding error, bounded in
`𝕋`, plus the error box of the result. -/
def Zonotope.plusBox (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  (⟨fun i => subDown (addDown (Z₁.c i) (Z₂.c i)) (addUp (Z₁.c i) (Z₂.c i)),
      fun _ => zero⟩ : Interval (Vec 𝕋 n)).plus (Z₁.plus Z₂).I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
