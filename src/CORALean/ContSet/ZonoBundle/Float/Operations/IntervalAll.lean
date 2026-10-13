import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval
import CORALean.ContSet.Interval.Float.Operations.Intersection

/-!
# `ZonoBundle.intervalAll`, over a floating-point scalar

The box of a whole bundle: the intersection of every member's box, starting from the first
member's, as at the exact layer. Each member's box is rounded outward by `Zonotope.interval`,
and the intersection of float boxes rounds nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The intersection of every member's box, starting from the first member's. -/
def ZonoBundle.intervalAll (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) : Interval (Vec 𝕋 n) :=
  (List.finRange zB.k).foldl (fun I i => Interval.intersection I (Zonotope.interval (zB.Z i)))
    (Zonotope.interval (zB.Z ⟨0, hk⟩))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
