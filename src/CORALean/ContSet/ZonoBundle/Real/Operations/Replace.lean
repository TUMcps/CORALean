module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.replace`

CORA's `zonoBundle`/`replace(zB, index, Z)`: the `index`-th zonotope of the bundle is overwritten by
`Z` (`zB.Z{index} = Z`), the others kept and the count unchanged.

## Inputs
* `zB` – zonotope bundle
* `index` – member to overwrite
* `Z` – replacement zonotope

## Output
* the bundle with that member replaced
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonoBundle/replace`. -/
def ZonoBundle.replace (zB : ZonoBundle α) (index : Fin zB.k) (Z : Zonotope α) : ZonoBundle α where
  k := zB.k
  Z := Function.update zB.Z index Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
