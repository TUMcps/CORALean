import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.InteriorPoint

/-!
# `ZonoBundle.isFullDim`, over a floating-point scalar

CORA's `@zonoBundle/isFullDim` tests the intersection through `polytope(zB)`. Here a point `x₀`
and one right inverse `Hᵢ` per member are the caller's, and checked: every member must hold `x₀`
strictly inside a box it contains (`Zonotope.interiorPoint`). The members are open around `x₀`,
so their finite intersection is, and `x₀` is an interior point. `true` proves it; `false` refutes
nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.isFullDim (zB : ZonoBundle (Vec 𝕋 n)) (H : (i : Fin zB.k) → Mat 𝕋 (zB.Z i).h n)
    (x₀ : Vec 𝕋 n) : Bool :=
  (List.finRange zB.k).all fun i => Zonotope.interiorPoint (zB.Z i) (H i) x₀

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
