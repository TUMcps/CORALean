import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# `Zonotope.plusBox`

What `plus` can add beyond the Minkowski sum of its two operands' `construct`,
computed in `𝕋` with directed rounding rather than read back through `toReal`:
the centre's rounding gap — bounded the same two ways `addDown`/`addUp`
already bound it, `addDown` never exceeding the exact sum and `subDown`
against `addUp` never exceeding the gap below it — together with the result's
own error box unchanged. The generators never round — `plus` concatenates
them exactly — so this is the whole of it.

Not an operation `Reduce`-style: no class asks a representation for how far a
binary operation may overshoot its inputs, and only `plus`'s own definition
can say.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre's rounding gap, bounded in `𝕋`, together with the result's own
error box. -/
def Zonotope.plusBox (Z₁ Z₂ : Zonotope (Vec 𝕋 n)) : Interval (Vec 𝕋 n) :=
  (⟨fun i => subDown (addDown (Z₁.c i) (Z₂.c i)) (addUp (Z₁.c i) (Z₂.c i)),
      fun _ => zero⟩ : Interval (Vec 𝕋 n)).plus (Z₁.plus Z₂).E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
