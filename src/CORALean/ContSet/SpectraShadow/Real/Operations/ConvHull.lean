import CORALean.ContSet.SpectraShadow.Real.Operations.Cone
import CORALean.ContSet.SpectraShadow.Real.Operations.SingletonOne
import CORALean.ContSet.SpectraShadow.Real.Operations.HyperplaneOne
import CORALean.ContSet.SpectraShadow.Real.Operations.CartProd
import CORALean.ContSet.SpectraShadow.Real.Operations.Inter
import CORALean.ContSet.SpectraShadow.Real.Operations.Project

/-!
# `SpectraShadow.convHull_`

CORA's `convHull_(SpS, S)` for two spectrahedral shadows (`@spectraShadow/convHull_.m`), following
its printed steps: both are put at height `1` by `cartProd_` with the singleton `{1}`, their conic
hulls `aux_conicHull` (`cone`) are added, the sum is cut with the hyperplane `Rn_x_1 = ℝⁿ × {1}` and
projected to the first `n` coordinates. `Theorems.ConvHullExact` says the result is exactly the
convex hull of the union. CORA assembles the cones from the SVD form of each shadow
(`generateESumRep`); the cone here works from the representation as stored. CORA's early returns for
`isemptyobject` operands are not needed: the cone of an empty shadow is the origin, and the hull of
`∅` and `S` is `S`.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.convHull_ (SpS S : SpectraShadow (Vec ℝ n)) : SpectraShadow (Vec ℝ n) :=
  let singleton : SpectraShadow (Vec ℝ 1) := SpectraShadow.singletonOne
  let Rn_x_1 : SpectraShadow (Vec ℝ (n + 1)) := SpectraShadow.hyperplaneOne n
  let S1_x_1 : SpectraShadow (Vec ℝ (n + 1)) := SpS.cartProd singleton
  let S2_x_2 : SpectraShadow (Vec ℝ (n + 1)) := S.cartProd singleton
  let cone_S1 : SpectraShadow (Vec ℝ (n + 1)) := S1_x_1.cone
  let cone_S2 : SpectraShadow (Vec ℝ (n + 1)) := S2_x_2.cone
  let cone_sum : SpectraShadow (Vec ℝ (n + 1)) := cone_S1.plus cone_S2
  (cone_sum.inter Rn_x_1).project (Fin.castAdd 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
