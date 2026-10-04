import CORALean.ContDynamics.LinearSysDT.Definitions.GO
import CORALean.ContSet.Interval.Float.Interval

/-!
# The GO parameters as interval matrices

`LinearSysDT.GO` holds real matrices, which a float run cannot name. `GOFloat` holds, in their
place, interval matrices over `𝕋` that enclose them: the parameters `A{k}`, `B{k,j}`, `C{k}`,
`D{k,j}` of `computeGO`, each entry rounded outward.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSysDT.GOFloat (𝕋 : Type) (n r nk : ℕ) where
  A : Fin nk → Interval (Mat 𝕋 n n)
  B : Fin nk → Fin nk → Interval (Mat 𝕋 n n)
  C : Fin nk → Interval (Mat 𝕋 r n)
  D : Fin nk → Fin nk → Interval (Mat 𝕋 r n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
