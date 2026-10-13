module

public import CORALean.Global.Float.FloatOps
public import CORALean.NN.Layers.Operations.AllOver

@[expose] public section

/-!
# A proposed sample grid, certified

The grid is not computed, it is *checked*. Rounding is constrained in one direction per
operation, so no expression can be proved to step by a bounded amount; a caller proposes the
samples, and this certifies them with `le` alone: the left end reached, every gap and the
right end within `dx`, every sample inside the box. A grid that fails yields no bracket rather
than a wrong one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The left end reached, every gap and the right end within `dx`, every sample in the box. -/
def gridChecked (p : Fin (N + 1) → 𝕋) (l u dx : 𝕋) : Bool :=
  le (p 0) l && allOver (fun j : Fin N => le (subUp (p j.succ) (p j.castSucc)) dx)
    && le (subUp u (p (Fin.last N))) dx
    && allOver fun i : Fin (N + 1) => le l (p i) && le (p i) u

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
