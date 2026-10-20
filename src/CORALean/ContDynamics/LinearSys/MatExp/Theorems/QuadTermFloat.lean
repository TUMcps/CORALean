module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `γ(a)` lies in `quadTerm t a`

`a t` lies between its two directed products, and `γ = m + m²/2` with `m = a t`, so the corner
hull of `m · m` and the two directed sums enclose it.

## Inputs
* `t` – float time
* `a` – float diagonal entry

## Hypotheses
* none

## Conclusion
* the float interval brackets the exact diagonal factor
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.quadTerm_mem (t a : 𝕋) : -- --- CONCL ---
    toReal (MatExp.quadTerm t a).inf ≤ Real.MatExp.quadTerm (toReal t) (toReal a)
      ∧ Real.MatExp.quadTerm (toReal t) (toReal a) ≤
        toReal (MatExp.quadTerm t a).sup := by -- --- PROOF ---
  have hm1 := mulDown_le_mul a t
  have hm2 := mul_le_mulUp a t
  have hsq := Interval.mul_between_corners hm1 hm2 hm1 hm2
  have hγ : Real.MatExp.quadTerm (toReal t) (toReal a)
      = toReal a * toReal t + (toReal a * toReal t) * (toReal a * toReal t) / 2 := by
    simp only [Real.MatExp.quadTerm]; ring
  rw [hγ]
  simp only [MatExp.quadTerm]
  constructor
  · refine le_trans (addDown_le_add _ _) ?_
    rw [toReal_half]
    linarith [hsq.1]
  · refine le_trans ?_ (add_le_addUp _ _)
    rw [toReal_half]
    linarith [hsq.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
