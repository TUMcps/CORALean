module

public import CORALean.ContSet.Interval.Float.Operations.Dirac
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Interval.dirac` contains `0`, over a floating-point scalar

For every order `n`, the result contains `0` in every coordinate (`δ⁽ⁿ⁾` vanishes off `0`): each
stored lower bound is at most `0`, each stored upper bound at least `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.dirac_zero_mem (n : ℕ) (I : Interval (Vec 𝕋 m)) (i : Fin m) :
    (∀ l, (Interval.dirac n I).lo i = some l → toReal l ≤ 0) ∧
      ∀ u, (Interval.dirac n I).hi i = some u → 0 ≤ toReal u := by -- --- PROOF ---
  unfold Interval.dirac
  constructor
  · intro l hl
    -- a stored bound is the float `zero`
    dsimp only at hl
    split_ifs at hl
    cases Option.some.inj hl
    rw [toReal_zero]
  · intro u hu
    dsimp only at hu
    split_ifs at hu
    cases Option.some.inj hu
    rw [toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
