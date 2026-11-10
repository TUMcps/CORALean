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


-- ====================================  `isBounded_toSet`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Compact, hence bounded: the nominal part's compactness and the box's are carried
across the sum by `isCompact_toSet`. -/
theorem isBounded_toSet [CompactSet N (Vec ℝ n)] (s : S) :
    Bornology.IsBounded (toSet s) :=
  (isCompact_toSet s).isBounded


-- ================================  `nominalSet_subset_toSet`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A box that holds the origin leaves the nominal set inside the whole: what an operation that
has moved its box into its parameters (`absorbRounding`) leaves behind. -/
theorem nominalSet_subset_toSet {s : S} (h : (0 : Vec ℝ n) ∈ (I_error s).toSet) :
    nominalSet s ⊆ toSet s := fun x hx => ⟨x, hx, 0, h, add_zero x⟩

end CORALean.Float.InflatedContSet


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
