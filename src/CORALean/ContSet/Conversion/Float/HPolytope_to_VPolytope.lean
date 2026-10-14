module

public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_VPolytope

@[expose] public section

/-!
# Halfspaces to vertices, over a floating-point scalar

Through a box, as in the exact layer: `2n` certified bounds, then `2ⁿ` corners.
The rounding has all been paid by the time the bounds arrive, and copying them
into corners costs nothing more.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.vPolytopeBox_contains (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.vPolytopeBox up lo).construct :=
  subset_trans (HPolytope.interval_contains up lo) (Interval.vPolytope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
