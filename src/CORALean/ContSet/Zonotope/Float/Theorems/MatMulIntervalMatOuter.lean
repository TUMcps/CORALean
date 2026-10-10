import CORALean.ContSet.Zonotope.Float.Operations.MatMulIntervalMat
import CORALean.ContSet.Zonotope.Float.Theorems.MatMulOuter
import CORALean.ContSet.Zonotope.Float.Theorems.OfIntervalMatOuter

/-!
# `GZonotope.matMulIntervalMat` over-approximates every product

`ofIntervalMat_outer` places the interval factor's member in its matrix zonotope, and
`matMul_outer` does the rest.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GZonotope.matMulIntervalMat_outer (M : GZonotope (Mat 𝕋 p q)) (I : Interval (Mat 𝕋 q r)) :
    (⋃ A ∈ M.construct, (A * ·) '' I.construct)
      ⊆ (GZonotope.matMulIntervalMat M I).construct := by
  refine subset_trans ?_ (GZonotope.matMul_outer M (GZonotope.ofIntervalMat I))
  refine Set.iUnion₂_mono fun A _ => ?_
  exact Set.image_mono (GZonotope.ofIntervalMat_outer I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
