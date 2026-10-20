module

public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread

@[expose] public section

/-!
# A monotone function's slope-zero relaxation is sound

Between its values at the box's ends a monotone `σ` stays, and those are bracketed by the
enclosure, so `σ t` lies between two stored values and `abs_sub_le_spread` bounds its distance
from the midpoint by the stored error.

## Inputs
* `E` – enclosure of the monotone function

## Hypotheses
* `hσ` – the function is monotone
* `hE` – enclosure is sound for the function

## Conclusion
* the slope-zero relaxation is sound for the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.ofMonotone_sound {E : Enclosure 𝕋} (hσ : Monotone σ)
    (hE : E.Sound σ) : -- --- CONCL ---
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
