import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# A scalar interval function encloses a real function
`ScalarEncloses E f`: for every box `I` and every real `x` in it, `f x` lies in the box `E I`.
It is what an activation's stored enclosure owes the real activation or derivative it stands for.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


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
