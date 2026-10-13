import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Data.Finset.Lattice.Fold

/-!
# `Interval.enclosePoints`

CORA's `@interval/enclosePoints`: the smallest box containing a finite, nonempty family of
points, the coordinatewise minimum and maximum (CORA's `min(points,[],2)`, `max(points,[],2)`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.enclosePoints {κ : Type} [Fintype κ] [Nonempty κ] (p : κ → α) : Interval α where
  inf := ofEntry fun i => Finset.univ.inf' Finset.univ_nonempty fun k => entry (p k) i
  sup := ofEntry fun i => Finset.univ.sup' Finset.univ_nonempty fun k => entry (p k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
