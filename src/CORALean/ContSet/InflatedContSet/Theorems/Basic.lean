module

public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

@[expose] public section

/-!
# `ContSet/InflatedContSet/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float.InflatedContSet

open Pointwise

variable {𝕋 S N : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} [ContSet N (Vec ℝ n)]
variable [InflatedContSet S N (Vec 𝕋 n) (Vec ℝ n)]


-- ==================================  `isBounded_construct`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Compact, hence bounded: the nominal part's compactness and the box's are carried
across the sum by `isCompact_construct`. -/
theorem isBounded_construct [CompactSet N (Vec ℝ n)] (s : S) :
    Bornology.IsBounded (construct s) :=
  (isCompact_construct s).isBounded

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
