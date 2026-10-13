module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Intersection
public import CORALean.ContSet.Conversion.Float.ConPolyZono_to_Interval
public import CORALean.ContSet.Conversion.Float.Interval_to_ConPolyZono
public import CORALean.ContSet.Interval.Float.Operations.SplitAt

@[expose] public section

/-!
# `ConPolyZono.split`, over a floating-point scalar

The set intersected with the two halves of its bounding box along dimension `d`, as over ℝ:
the box is `ConPolyZono.interval`, cut by `Interval.splitAt`, each half converted by
`Interval.conPolyZono` and intersected with the set by the float `intersection`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.split (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (d : Fin n) :
    ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n) :=
  let I := cPZ.interval
  -- the box cut at the middle of side `d`
  let (I₁, I₂) := I.splitAt d
  (cPZ.intersection I₁.conPolyZono, cPZ.intersection I₂.conPolyZono)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
