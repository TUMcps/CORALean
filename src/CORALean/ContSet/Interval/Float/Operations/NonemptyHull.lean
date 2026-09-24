import CORALean.ContSet.Interval.Float.Interval

/-!
# A box made nonempty

The upper bound raised to the lower one wherever the two cross, and left alone elsewhere: the
smallest change that makes the box nonempty, and none at all to one that already is. What a
layer committing to a point of its error box runs on, when nothing proves the box nonempty.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.nonemptyHull (I : Interval 𝕋 n) : Interval 𝕋 n :=
  ⟨I.inf, fun i => maximum (I.inf i) (I.sup i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
