import CORALean.NN.Layers.Operations.RelaxationOfMonotone
import CORALean.NN.Layers.Theorems.AbsSubLeSpread

/-!
# A monotone function's slope-zero relaxation is sound

Between its values at the box's ends a monotone `σ` stays, and those are bracketed by the
enclosure, so `σ t` lies between two stored values and `abs_sub_le_spread` bounds its distance
from the midpoint by the stored error.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.ofMonotone_sound {E : Enclosure 𝕋} (hσ : Monotone σ) (hE : E.Sound σ) :
    (Relaxation.ofMonotone E).Sound σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  have hlo : toReal (E.lo l) ≤ σ t := le_trans (hE.lo_le l) (hσ hl)
  have hhi : σ t ≤ toReal (E.hi u) := le_trans (hσ hu) (hE.le_hi u)
  have h := abs_sub_le_spread (c := E.mid l u) hlo hhi
  show |σ t - (toReal (FloatOps.zero : 𝕋) * t + toReal (E.mid l u))| ≤ _
  rw [toReal_zero, zero_mul, zero_add]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
