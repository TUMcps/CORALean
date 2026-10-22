module

public import CORALean.NN.Layers.Operations.RelaxationOfMonotone
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread

@[expose] public section

/-!
# A monotone function's slope-zero relaxation is sound where its enclosure is

`Relaxation.ofMonotone_sound` for an enclosure that brackets `σ` only on some boxes, as `expUp`
does only under `2ⁿ/2`.

## Inputs
* `E` – enclosure of the monotone function
* `P` – condition on the box

## Hypotheses
* `hσ` – the function is monotone on boxes satisfying the condition
* `hlo` – lower end brackets the function at the left end
* `hhi` – upper end brackets the function at the right end

## Conclusion
* the slope-zero relaxation is sound where the condition holds
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same, where the enclosure brackets `σ` only on the boxes `P` holds on: the lower end at
the box's left end, the upper one at its right. -/
theorem Relaxation.ofMonotone_soundWhere {E : Enclosure 𝕋} {P : 𝕋 → 𝕋 → Prop}
    (hσ : ∀ l u, P l u → Monotone σ)
    (hlo : ∀ l u, P l u → toReal (E.enclose l).inf ≤ σ (toReal l))
    (hhi : ∀ l u, P l u → σ (toReal u) ≤ toReal (E.enclose u).sup) : -- --- CONCL ---
    (Relaxation.ofMonotone E).SoundWhere σ P := by -- --- PROOF ---
  refine ⟨fun {l u t} hP hl hu => ?_⟩
  have hlo' : toReal (E.enclose l).inf ≤ σ t := le_trans (hlo l u hP) (hσ l u hP hl)
  have hhi' : σ t ≤ toReal (E.enclose u).sup := le_trans (hσ l u hP hu) (hhi l u hP)
  have h := abs_sub_le_spread (c := E.mid l u) hlo' hhi'
  show |σ t - (toReal (FloatOps.zero : 𝕋) * t + toReal (E.mid l u))| ≤ _
  rw [toReal_zero, zero_mul, zero_add]
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
