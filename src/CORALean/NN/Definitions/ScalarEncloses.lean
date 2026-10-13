module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A scalar interval function encloses a real function
`ScalarEncloses E f`: for every box `I` and every real `x` in it, `f x` lies in the box `E I`.
It is what an activation's stored enclosure owes the real activation or derivative it stands for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def ScalarEncloses (E : Interval 𝕋 → Interval 𝕋) (f : ℝ → ℝ) : Prop :=
  ∀ (I : Interval 𝕋) (x : ℝ), toReal I.inf ≤ x → x ≤ toReal I.sup →
    toReal (E I).inf ≤ f x ∧ f x ≤ toReal (E I).sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
