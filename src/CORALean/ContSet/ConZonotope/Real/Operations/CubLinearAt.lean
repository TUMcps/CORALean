import CORALean.ContSet.Zonotope.Real.Operations.CubIdx
import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Reading coefficients off the generators of `Zonotope.cubMap`

The constraint of a constrained zonotope sits on its *linear* factors: the generators whose
monomial is a single old factor, `(0, 0, j)` for `cubMap`, and the `((0, 0), a)`, `((0, b), 0)` and
`((j, 0), 0)` of the three families of `cubMapMixed`. `cubLinearAt t` reads the coefficients of
the generators `t j` off a coefficient vector of the zonotope `cubMap`; the constraint polytope
of the old factors, pulled back along it, is the constraint of the result.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficients at the generators `t j` of a coefficient vector indexed as `cubIdx`. -/
def ConZonotope.cubLinearAt (N₁ N₂ N₃ : ℕ) (t : Fin h → (Fin N₁ × Fin N₂) × Fin N₃) :
    Vec ℝ (N₁ * N₂ * N₃) →ₗ[ℝ] Vec ℝ h where
  toFun γ j := γ ((Zonotope.cubIdx N₁ N₂ N₃).symm (t j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
