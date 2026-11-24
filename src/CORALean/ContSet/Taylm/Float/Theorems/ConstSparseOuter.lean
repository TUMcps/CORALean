module

public import CORALean.ContSet.Taylm.Float.Operations.ConstSparse
public import CORALean.ContSet.Taylm.Float.Theorems.Basic

@[expose] public section

/-!
# `Taylm.constSparse` encloses the constant

Its polynomial is the constant itself, at every point, and its remainder and error box are zero.

## Inputs
* `n` – number of variables
* `c` – the constant
* `N` – the order `times` truncates to

## Hypotheses
* none

## Conclusion
* the model encloses the constant function `c`, and its polynomial is `c` everywhere
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.constSparse_outer (n : ℕ) (c : 𝕋) (N : ℕ) : -- --- CONCL ---
    (Taylm.constSparse n c N).Encloses (fun _ => toReal c) ∧
      ∀ t, (Taylm.constSparse n c N).inflated.poly t = toReal c ∧
        toReal (Taylm.constSparse n c N).rem.inf = 0 ∧
        toReal (Taylm.constSparse n c N).rem.sup = 0 ∧
        toReal (Taylm.constSparse n c N).I_error.inf = 0 ∧
        toReal (Taylm.constSparse n c N).I_error.sup = 0 := by -- --- PROOF ---
  unfold Taylm.constSparse
  split
  · -- a certified zero: no term, and the constant is zero
    rename_i h
    simp only [Bool.and_eq_true] at h
    have h0 : toReal c = 0 :=
      le_antisymm (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h.1)
        (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le h.2)
    refine ⟨fun t _ => ?_, fun t => ?_⟩ <;>
      simp [Taylm.inflated, Real.Taylm.poly, Real.Taylm.polyOf, toReal_zero, h0]
  · refine ⟨Taylm.const_outer c N, fun t => ?_⟩
    simp [Taylm.const, Taylm.inflated, Real.Taylm.poly, Real.Taylm.polyOf,
      Real.Taylm.monomial_zero, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
