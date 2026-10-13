module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.Bilin
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadBilin

@[expose] public section

/-!
# `ZonoBundle.quadMap`

CORA's `zonoBundle`/`quadMap(zB, Q)`: every member `Z{i}` is replaced by `quadMap(Z{i}, Q)`, the
zonotope quadratic map, which is `Zonotope.bilin` at the quadratic-form family
`PolyZonotope.quadBilin Q` (`x ↦ y ↦ (xᵀ Q_k y)_k`) applied to the member with itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle/quadMap`: member-wise. -/
def ZonoBundle.quadMap (Q : Fin m → Mat ℝ n n) (zB : ZonoBundle (Vec ℝ n)) :
    ZonoBundle (Vec ℝ m) where
  k := zB.k
  Z := fun i => Zonotope.bilin (PolyZonotope.quadBilin Q) (zB.Z i) (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
