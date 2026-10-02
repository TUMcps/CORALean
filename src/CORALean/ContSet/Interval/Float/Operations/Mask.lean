import CORALean.ContSet.Interval.Float.Interval

/-!
# `Interval.mask` over floats

Entries outside the pattern become the float `zero`; the rest are moved, not computed on, so
nothing is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.mask (keep : Fin m → Fin n → Prop) [∀ i j, Decidable (keep i j)]
    (I : Interval (Mat 𝕋 m n)) : Interval (Mat 𝕋 m n) where
  inf := fun i j => if keep i j then I.inf i j else zero
  sup := fun i j => if keep i j then I.sup i j else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
