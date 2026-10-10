import CORALean.ContSet.Interval.Float.Operations.Dirac

/-!
# `Interval.dirac` is `{0}` off `0`, over a floating-point scalar

In a coordinate the strict tests certify to miss `0`, the result is `{0}`, for every order `n`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [SoundFloatArithmetic 𝕋] in
theorem Interval.dirac_eq_zero_of_off (n : ℕ) (I : Interval (Vec 𝕋 m)) (i : Fin m)
    (h : (ltStrict zero (I.inf i) || ltStrict (I.sup i) zero) = true) :
    (Interval.dirac n I).lo i = some zero ∧ (Interval.dirac n I).hi i = some zero := by
  rcases Bool.or_eq_true_iff.1 h with h | h <;> simp [Interval.dirac, h]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
