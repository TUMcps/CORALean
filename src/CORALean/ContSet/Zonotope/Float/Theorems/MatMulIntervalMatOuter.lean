import CORALean.ContSet.Zonotope.Float.Operations.MatMulIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Float.Theorems.OfIntervalMatOuter

/-!
# `Zonotope.matMulIntervalMat` over-approximates every product

`ofIntervalMat_outer` places the interval factor's member in its matrix zonotope, and
`matMul_outer` does the rest.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matMulIntervalMat_outer (M : Zonotope (Mat 𝕋 p q)) (I : Interval (Mat 𝕋 q r)) :
    (⋃ A ∈ M.construct, (A * ·) '' I.construct)
      ⊆ (Zonotope.matMulIntervalMat M I).construct := by
  refine subset_trans ?_ (Zonotope.matMul_outer M (Zonotope.ofIntervalMat I))
  refine Set.iUnion₂_mono fun A _ => ?_
  exact Set.image_mono (Zonotope.ofIntervalMat_outer I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
