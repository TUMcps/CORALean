import Mathlib.Algebra.Group.Defs

/-!
# CORA's `params` for a system with an input set

`Reach.Params` with CORA's `params.U` after the initial set, so `⟨R₀, U, 0, k⟩`
reads as CORA's `R0`, `U`, `tStart`, `tFinal`.

CORA defaults `U` to the origin when absent. Here the default is the choice of
structure rather than a value: an input-free algorithm — `LinearSys.reachFloat`,
CORA's `isU` branch with nothing to add — takes `Reach.Params`, and an algorithm
with an input term takes this one, `U` mandatory, so a missing input set is never
filled in silently. A caller who means the origin writes it, at whatever
representation `U` is.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The initial set `R0`, the input set `U` and the horizon `[tStart, tFinal]`:
CORA's `params.R0`, `params.U`, `params.tStart` (default `0`), `params.tFinal`. -/
structure Reach.InputParams (X I T : Type) [Zero T] where
  R0 : X
  U : I
  tStart : T := 0
  tFinal : T

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
