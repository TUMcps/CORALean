module

public import CORALean.ContSet.HPolytope.Float.Operations.DualBound
public import CORALean.ContSet.Interval.Float.Operations.OfBounds
public import CORALean.ContSet.Interval.Float.Operations.SubsetOfBounds

@[expose] public section

/-!
# A halfspace description as a box, over a floating-point scalar — the construction

`HPolytope.interval` is the construction; `HPolytope_to_Interval` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {P : HPolytope 𝕋 (Vec 𝕋 n)}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.interval (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : Interval (Vec 𝕋 n) :=
  Interval.ofBounds up lo

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
