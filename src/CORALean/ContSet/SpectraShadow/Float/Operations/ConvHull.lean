import CORALean.ContSet.SpectraShadow.Float.Operations.Cone
import CORALean.ContSet.SpectraShadow.Float.Operations.SingletonOne
import CORALean.ContSet.SpectraShadow.Float.Operations.HyperplaneOne
import CORALean.ContSet.SpectraShadow.Float.Operations.CartProd
import CORALean.ContSet.SpectraShadow.Float.Operations.Inter
import CORALean.ContSet.SpectraShadow.Float.Operations.Project

/-!
# `SpectraShadow.convHull_`, over a floating-point scalar

CORA's `convHull_(SpS, S)` for two spectrahedral shadows, as the exact layer has it
(`Real.SpectraShadow.convHull_`), with the float `cartProd`, `cone`, `plus`, `inter` and `project`:
both shadows at height `1` (`singletonOne`), their cones added, the sum cut with the hyperplane `ℝⁿ
× {1}` (`hyperplaneOne`) and projected to the first `n` coordinates. The only rounding is `plus`'s
on the centre, which its box takes; the shadows' own boxes are absorbed by the cones. Each stage is
`materialise`d (stored, `materialise_eq`), as the fields are function types.
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.convHull_ (SpS S : SpectraShadow 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  let singleton : SpectraShadow 𝕋 (Vec 𝕋 1) := SpectraShadow.singletonOne
  let Rn_x_1 : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := SpectraShadow.hyperplaneOne 𝕋 n
  let S1_x_1 : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := (SpS.cartProd singleton).materialise
  let S2_x_2 : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := (S.cartProd singleton).materialise
  let cone_S1 : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := S1_x_1.cone.materialise
  let cone_S2 : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := S2_x_2.cone.materialise
  let cone_sum : SpectraShadow 𝕋 (Vec 𝕋 (n + 1)) := (cone_S1.plus cone_S2).materialise
  ((cone_sum.inter Rn_x_1).materialise.project (Fin.castAdd 1)).materialise

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
