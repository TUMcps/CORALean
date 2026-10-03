import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The factors of the derivatives of `√`

`√⁽ᵏ⁾ x = (1/2)(1/2 - 1)⋯(1/2 - k + 1) · x^(1/2 - k)`, the product `∏ᵢ<ₖ (1/2 - i)` being the
integer `sqrtDeriv k = ∏ᵢ<ₖ (1 - 2i)` over `2ᵏ`: the computable form of the real `descPochhammer`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def sqrtDeriv : ℕ → ℤ
  | 0 => 1
  | k + 1 => sqrtDeriv k * (1 - 2 * (k : ℤ))

theorem eval_descPochhammer_half (k : ℕ) :
    (descPochhammer ℝ k).eval (1 / 2) = (sqrtDeriv k : ℝ) / 2 ^ k := by -- --- PROOF ---
  induction k with
  | zero => simp [sqrtDeriv]
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, sqrtDeriv]
    push_cast
    field_simp
    ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
