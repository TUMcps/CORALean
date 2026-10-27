module

public import CORALean.NN.Layers.Operations.RelaxationOfAntitone
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread

@[expose] public section

/-!
# An antitone function's slope-zero relaxation is sound

Between its values at the box's right and left ends an antitone `σ` stays, and those are
bracketed by the enclosure, so `abs_sub_le_spread` bounds `σ t`'s distance from the stored
midpoint by the stored error.

## Inputs
* `E` – enclosure of the antitone function

## Hypotheses
* `hσ` – the function is antitone
* `hE` – enclosure is sound for the function

## Conclusion
* the slope-zero relaxation is sound for the function
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Relaxation.ofAntitone_encloses {E : Enclosure 𝕋} (hσ : Antitone σ)
    (hE : E.Encloses σ) : -- --- CONCL ---
    (Relaxation.ofAntitone E).Encloses σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  have hlo : toReal (E.enclose u).inf ≤ σ t := le_trans (hE.lo_le u) (hσ hu)
  have hhi : σ t ≤ toReal (E.enclose l).sup := le_trans (hσ hl) (hE.le_hi l)
  have h := abs_sub_le_spread (c := half (addUp (E.enclose u).inf (E.enclose l).sup)) hlo hhi
  show |σ t - (toReal (FloatOps.zero : 𝕋) * t +
    toReal (half (addUp (E.enclose u).inf (E.enclose l).sup)))| ≤ _
  rw [toReal_zero, zero_mul, zero_add]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
