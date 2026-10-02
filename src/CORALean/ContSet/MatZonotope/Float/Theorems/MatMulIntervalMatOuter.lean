import CORALean.ContSet.MatZonotope.Float.Operations.MatMulIntervalMat
import CORALean.ContSet.MatZonotope.Float.Theorems.MatMulOuter
import CORALean.ContSet.MatZonotope.Float.Theorems.OfIntervalOuter

/-!
# `MatZonotope.matMulIntervalMat` over-approximates every product

`ofInterval_outer` places the interval factor's member in its matrix zonotope, and
`matMul_outer` does the rest.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatZonotope.matMulIntervalMat_outer (M : MatZonotope 𝕋 p q) (I : Interval (Mat 𝕋 q r)) :
    (⋃ A ∈ M.construct, (A * ·) '' I.construct)
      ⊆ (MatZonotope.matMulIntervalMat M I).construct := by
  refine subset_trans ?_ (MatZonotope.matMul_outer M (MatZonotope.ofInterval I))
  refine Set.iUnion₂_mono fun A _ => ?_
  exact Set.image_mono (MatZonotope.ofInterval_outer I)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
