import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul

/-!
# `Zonotope.intersectStrip`

CORA's `@zonotope/intersectStrip` for a numeric weight matrix `Λ` (`aux_zonotopeFromLambda`,
Prop. 1 of Le et al., ISIC 2013). The strips `|C x - y| ≤ φ` meet the zonotope `c + G [-1, 1]^h`
in a set that the zonotope with centre `c + Λ (y - C c)` and generators
`[(I - Λ C) G, Λ diag(φ)]` encloses, whatever `Λ` is. Only this branch is modelled: the named
methods that choose `Λ` (`'normGen'`, `'svd'`, `'radius'`, `'alamo-volume'`, `'alamo-FRad'`,
`'wang-FRad'`, `'bravo'`) are tuning, as `Λ` is any matrix here, and the soundness does not depend
on it.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/intersectStrip` at the weights `Λ`: centre `c + Λ (y - C c)`, generators
`(I - Λ C) G_j` and then `Λ (φ_i e_i)`, the columns of `Λ diag(φ)`. -/
def Zonotope.intersectStrip (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let c_new : Vec ℝ n := Z.c + Λ *ᵥ (y - C *ᵥ Z.c)                  -- new centre
  let I : Mat ℝ n n := 1
  let G_old : Fin Z.h → Vec ℝ n := fun j => (I - Λ * C) *ᵥ Z.G j    -- (I - Λ C) G
  let G_strip : Fin p → Vec ℝ n := fun i => Λ *ᵥ Pi.single i (φ i)  -- Λ diag(φ)
  { h := Z.h + p
    c := c_new
    G := Fin.append G_old G_strip }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
