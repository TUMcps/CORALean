module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Theorems.PlusOuter

@[expose] public section

/-!
# `Taylm.sum` encloses the sum

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the sum model encloses the sum of the functions
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sum_outer : ∀ {m : ℕ} {T : Fin m → Taylm 𝕋 n} {f : Fin m → Vec ℝ n → ℝ},
    (∀ i, (T i).Encloses (f i)) → (Taylm.sum T).Encloses fun t => ∑ i, f i t := by -- --- PROOF ---
  intro m
  induction m with
  | zero => intro T f _ t _; simp [Taylm.sum, Taylm.inflated, Real.Taylm.poly, toReal_zero]
  | succ m ih =>
    intro T f h
    have := Taylm.plus_outer (h 0) (ih (T := fun i => T i.succ) (f := fun i => f i.succ)
      fun i => h i.succ)
    simpa only [Taylm.sum, Fin.sum_univ_succ] using this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
