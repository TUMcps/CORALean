import CORALean.ContSet.PolyZonotope.Real.Operations.CubMapDep
import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import Mathlib.LinearAlgebra.Prod

/-!
# `PolyZonotope.cubMapMixed`

The mixed form of CORA's `@polyZonotope/cubMap`, `cubMap(pZ₁, pZ₂, pZ₃, T)`:
`{ z = (x₁ᵀ T x₂) * x₃ | x₁ ∈ pZ₁, x₂ ∈ pZ₂, x₃ ∈ pZ₃ }`, `zᵢ = Σₖ (x₃)ₖ (x₁ᵀ T{i,k} x₂)`,
the arguments ranging independently. As `quadMapMixed` does it: the three sets (each made
dependent) are put side by side with disjoint factors, `cartProd`, and the cubic map reads its
three arguments off the projections. CORA's `mergeExpMatrix` instead unifies the factors by
identifier, so two arguments built on a common factor stay tied in CORA; the product here lets
them vary independently, which is what the set in the header is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_cubMapMixed`: the three sets side by side, the cubic map read off the projections. -/
def PolyZonotope.cubMapMixed (T : Fin m → Fin n → Mat ℝ n n)
    (pZ₁ pZ₂ pZ₃ : PolyZonotope (Vec ℝ n)) : PolyZonotope (Vec ℝ m) :=
  PolyZonotope.cubMapDepOn
    ((LinearMap.fst ℝ (Vec ℝ n) (Vec ℝ n)).comp (LinearMap.fst ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)))
    ((LinearMap.snd ℝ (Vec ℝ n) (Vec ℝ n)).comp (LinearMap.fst ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)))
    (LinearMap.snd ℝ (Vec ℝ n × Vec ℝ n) (Vec ℝ n)) T
    ((pZ₁.dependent.cartProd pZ₂.dependent).cartProd pZ₃.dependent)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
