module

public import CORALean.ContDynamics.LinearARX.Definitions.GO
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The output GO parameters as interval matrices

`LinearARX.GO` holds real matrices, which a float run cannot name. `GOFloat` holds, in their place,
interval matrices over `𝕋` that enclose them: the parameters `C{k}` and `D{k,i}` of `computeGO`,
each entry rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

structure LinearARX.GOFloat (𝕋 : Type) (dy du p nk : ℕ) where
  C : Fin nk → Interval (Mat 𝕋 dy (p * dy))
  D : Fin nk → Fin nk → Interval (Mat 𝕋 dy du)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
