import CORALean.ContSet.ConZonotope.Real.Operations.KeepSplit
import CORALean.ContSet.ConZonotope.Real.Operations.ReduceKeepBy

/-!
# `ConZonotope.reduceKeep`

A reduction that keeps the constraints. Above the requested order, `keepSplit` ranks
the generators, `reduceKeepBy` boxes the lowest ranked and projects the constraints
onto what is kept; at or below it nothing happens.

Beside `ConZonotope.reduce`, not in place of it: that one drops `P` and reduces by
Girard's metric alone, this one ranks constrained generators first, so neither set
contains the other in general. What this one buys is that every constraint on a
kept coefficient survives, up to the slack `keepSlack` charges for a dropped one.
No linear program runs in either.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Above order `o`, box all but `(o - 1) * n` generators and keep the constraints on
the rest; at or below it, the identity. -/
noncomputable def ConZonotope.reduceKeep (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    ConZonotope (Vec ℝ n) :=
  if hlt : o * n < cZ.h then cZ.reduceKeepBy (cZ.keepSplit o hlt) else cZ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
