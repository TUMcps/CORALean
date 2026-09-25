import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
import CORALean.ContSet.Interval.Float.Operations.MatPlus
import CORALean.ContSet.Interval.Float.Operations.MatPow
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# `MatExp.expIntervalTaylor`, over a floating-point scalar

`Real.MatExp.expIntervalTaylor` rounded: `i = 0 … η` matching that recursion
term by term, each term `Interval.smul` at `invFactorialBounds i` — the float
layer's only handle on `1/i!`, which no float exactly holds.

Each partial sum is `materialiseMat`d before the next term is added to it, for
the reason `Interval.matPow`'s own recursion is: left as a closure, `η` nested
`matPlus`es would rebuild the whole sum on every entry read.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def MatExp.expIntervalTaylor (A : Interval (Mat 𝕋 n n)) : ℕ → Interval (Mat 𝕋 n n)
  | 0 => Interval.smul (MatExp.invFactorialBounds 0).1 (MatExp.invFactorialBounds 0).2
      (Interval.matPow A 0)
  | k + 1 => (Interval.matPlus
      (Interval.smul (MatExp.invFactorialBounds (k + 1)).1 (MatExp.invFactorialBounds (k + 1)).2
        (Interval.matPow A (k + 1)))
      (MatExp.expIntervalTaylor A k)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
