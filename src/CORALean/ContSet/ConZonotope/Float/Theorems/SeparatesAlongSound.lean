import CORALean.ContSet.ConZonotope.Float.Operations.SeparatesAlong
import CORALean.ContSet.ConZonotope.Float.Theorems.BoundDotLe

/-!
# `ConZonotope.separatesAlong` is sound when `true`

A direction along which the first set's upper bound lies strictly below the
second's lower bound leaves no point for both, whichever direction it is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.separatesAlong_sound {cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n)} {a : Vec 𝕋 n}
    (h : ConZonotope.separatesAlong cZ₁ cZ₂ a = true) :
    Disjoint cZ₁.construct cZ₂.construct := by -- --- PROOF ---
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hlt := toReal_lt_of_ltStrict h
  rw [toReal_neg] at hlt
  have h₁ := cZ₁.boundDot_le (c := rowLin (fun (_ : Fin 1) => a) 0) a (fun _ => rfl) x hx₁
  have h₂ := cZ₂.boundDot_le (c := rowLin (fun (_ : Fin 1) j => neg (a j)) 0)
    (fun j => neg (a j)) (fun _ => rfl) x hx₂
  have hneg : rowLin (fun (_ : Fin 1) j => neg (a j)) 0 x
      = -rowLin (fun (_ : Fin 1) => a) 0 x := by
    show ∑ j, toReal (neg (a j)) * x j = -∑ j, toReal (a j) * x j
    simp only [toReal_neg, neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at h₂
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
