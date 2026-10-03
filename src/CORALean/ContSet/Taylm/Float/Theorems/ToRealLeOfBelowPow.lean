import CORALean.ContSet.Taylm.Float.Operations.BelowPow
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# What `belowPow` certifies

`half` is exact, so `p` halvings divide by `2ᵖ`, and the comparison with `1/2` is one-sided
sound: a `true` check means `x ≤ 2ᵖ/2`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.toReal_le_of_belowPow {p : ℕ} {x : 𝕋} (h : Taylm.belowPow p x = true) :
    toReal x ≤ 2 ^ p / 2 := by -- --- PROOF ---
  have hit : ∀ k : ℕ, toReal (half^[k] x) = toReal x / 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ, div_div]
  have := toReal_le_of_le h
  rw [hit, toReal_half, toReal_one] at this
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  rw [div_le_iff₀ h2] at this
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
