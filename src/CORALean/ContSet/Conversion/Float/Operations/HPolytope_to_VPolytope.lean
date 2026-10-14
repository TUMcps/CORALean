module

public import CORALean.ContSet.Conversion.Float.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Float.HPolytope_to_Interval

@[expose] public section

/-!
# Halfspaces to vertices, over a floating-point scalar — the construction

`HPolytope.vPolytopeBox` is the construction; `HPolytope_to_VPolytope` states and proves what it
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

def HPolytope.vPolytopeBox (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope (HPolytope.interval up lo)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
