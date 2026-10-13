import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.matPlus`

`Interval.plus`'s counterpart at `Mat 𝕋 m n`: the float layer has no counterpart of
the exact layer's `Entrywise` class to state one addition generically over (see
`Interval.lean`), so the
matrix case gets its own name rather than overloading the `Vec` one. Each bound
rounds away from the interval, `inf` down and `sup` up, exactly as `plus` does.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matPlus (I₁ I₂ : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) where
  inf := fun i j => addDown (I₁.inf i j) (I₂.inf i j)
  sup := fun i j => addUp (I₁.sup i j) (I₂.sup i j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
