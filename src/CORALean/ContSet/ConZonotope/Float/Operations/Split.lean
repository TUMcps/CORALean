import CORALean.ContSet.ConZonotope.Float.Operations.Intersection
import CORALean.ContSet.Conversion.Float.ConZonotope_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_ConZonotope
import CORALean.ContSet.Interval.Float.Operations.SplitAt

/-!
# `ConZonotope.split`, over a floating-point scalar

The set intersected with the two halves of its bounding box along dimension `d`, as over ℝ:
the box is `ConZonotope.interval`, cut by `Interval.splitAt`, each half converted by
`Interval.conZonotope` and intersected with the set by the float `intersection`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.split (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    ConZonotope 𝕋 (Vec 𝕋 n) × ConZonotope 𝕋 (Vec 𝕋 n) :=
  let I := cZ.interval
  -- the box cut at the middle of side `d`
  let (I₁, I₂) := I.splitAt d
  (cZ.intersection I₁.conZonotope, cZ.intersection I₂.conZonotope)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
