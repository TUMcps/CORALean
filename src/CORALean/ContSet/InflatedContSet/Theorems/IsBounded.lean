import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

/-!
# An inflated representation of a compact set is bounded

Compact, hence bounded: the nominal part's compactness and the box's are carried
across the sum by `isCompact_construct`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
variable [ContSet N (Vec ℝ n)] [InflatedContSet S N 𝕋 n]


-- =======================================  MAIN THEOREM  ======================================= --

theorem isBounded_construct [CompactSet N (Vec ℝ n)] (s : S) :
    Bornology.IsBounded (construct s) :=
  (isCompact_construct s).isBounded

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
