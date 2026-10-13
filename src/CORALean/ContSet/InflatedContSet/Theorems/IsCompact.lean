import CORALean.ContSet.ContSet.Definitions.CompactSet
import CORALean.ContSet.InflatedContSet.InflatedContSet
import CORALean.ContSet.Interval.Real.Theorems.IsCompact
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# An inflated representation of a compact set is compact

A nominal set plus an error box, and `IsCompact.add` carries the property
across a Minkowski sum: the nominal part is compact by hypothesis and the box by
Heine–Borel. Compactness, not closedness, is what has to be carried: a sum of
two merely closed sets need not be closed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N (Vec 𝕋 n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem isCompact_construct [CompactSet N (Vec ℝ n)] (s : S) : IsCompact (construct s) :=
  IsCompact.add (CompactSet.isCompact_construct (nominal s)) (error s).nominal.isCompact_construct

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
