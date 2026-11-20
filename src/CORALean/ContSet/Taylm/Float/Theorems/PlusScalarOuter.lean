module

public import CORALean.ContSet.Taylm.Float.Operations.PlusScalar
public import CORALean.ContSet.Taylm.Float.Theorems.AccumTermLe
public import CORALean.ContSet.Taylm.Real.Theorems.Basic

@[expose] public section

/-!
# `Taylm.plusScalar` encloses the sum

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `s` – number

## Hypotheses
* `h` – `T` encloses `f`

## Conclusion
* the sum model encloses `f + s`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plusScalar_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (s : 𝕋) : -- --- CONCL ---
    (T.plusScalar s).Encloses fun t => f t + toReal s := by -- --- PROOF ---
  intro t ht
  have a := h t ht
  -- the constant term takes the number, up to the rounding bound
  have hS := abs_le.1 (Taylm.accumTerm_le T.terms s 0 ht)
  rw [Real.Taylm.monomial_zero, mul_one] at hS
  have := addDown_le_add T.I_error.inf (neg (Taylm.accumTerm T.terms s 0).2)
  have := add_le_addUp T.I_error.sup (Taylm.accumTerm T.terms s 0).2
  simp only [Taylm.plusScalar, Taylm.inflated, Real.Taylm.poly, subDown, toReal_neg] at *
  constructor <;> linarith [a.1, a.2, hS.1, hS.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
