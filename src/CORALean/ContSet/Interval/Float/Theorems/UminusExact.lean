module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.UminusExact

@[expose] public section

/-!
# `Interval.uminus` is exactly the negated set

Negation is exact, so the float box denotes the same set the exact layer's does.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the negated box represents exactly the negated set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.uminus_exact (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    -I.construct = I.uminus.construct := by -- --- PROOF ---
  have h : I.uminus.nominal = I.nominal.uminus := by
    unfold Interval.nominal Interval.uminus Real.Interval.uminus
    congr 1 <;> funext i <;> exact toReal_neg _
  show -I.nominal.construct = I.uminus.nominal.construct
  rw [h]
  exact Real.Interval.uminus_exact I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
