module

public import CORALean.ContDynamics.LinearSysDT.Definitions.GO
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The GO parameters as interval matrices

`LinearSysDT.GO` holds real matrices, which a float run cannot name. `GOFloat` holds, in their
place, interval matrices over `𝕋` that enclose them: the parameters `A{k}`, `B{k,j}`, `C{k}`,
`D{k,j}` of `computeGO`, each entry rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The general output model parameters of a discrete-time linear system, as interval matrices over
`𝕋`. -/
structure LinearSysDT.GOFloat (𝕋 : Type) (n r nk : ℕ) where
  A : Fin nk → Interval (Mat 𝕋 n n)
  B : Fin nk → Fin nk → Interval (Mat 𝕋 n n)
  C : Fin nk → Interval (Mat 𝕋 r n)
  D : Fin nk → Fin nk → Interval (Mat 𝕋 r n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
