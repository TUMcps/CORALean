import CORALean.ContSet.Zonotope.Float.Operations.ReduceBy
import CORALean.Global.Partition

/-!
# `Zonotope.reduceByBox`

The error `reduceBy` pays, computed in `𝕋`: `radius` already rounds up, so no
further rounding is owed. Centred at `0`, for the same reason `Real`'s is — the
dropped generators contribute `0` to `Z` when their coefficients are set to
`0`, so the reduced set never reaches further than `Z` plus this box — and
carrying a degenerate `0` error box of its own, `reduceBy` touching none.

Not a `Reduce` operation and no class instantiates it, as at `Real`.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box `reduceBy` absorbs the dropped generators into, on its own: one
generator per coordinate, the rounded-up absorbed rows' `1`-norm, centred at
the origin, with a degenerate error box of its own. -/
def Zonotope.reduceByBox (Z : Zonotope (Vec 𝕋 n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Zonotope (Vec 𝕋 n) where
  h := n
  c := fun _ => zero
  G := diagonalBlock (radius fun i l => Z.G (part.right l) i)
  E := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
