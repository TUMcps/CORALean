module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.ContSet.Operations.Enlarge

@[expose] public section

/-!
# `ZonoBundle.enlarge`

CORA's `@zonoBundle/enlarge.m`: each zonotope of the bundle is enlarged about its *own* center
(`enlarge(zB.Z{i}, factor)`), so the result is the intersection of the enlarged members, not the
enlargement of the intersection about a common center: the members' centers differ in general,
and so do the maps `x ↦ cᵢ + f ⊙ (x - cᵢ)`.

## Inputs
* `zB` – zonotope bundle
* `factor` – enlargement factor per coordinate

## Output
* the bundle with each member enlarged
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.enlarge (zB : ZonoBundle (Vec ℝ n)) (factor : Vec ℝ n) : ZonoBundle (Vec ℝ n) where
  k := zB.k
  Z := fun i => ContSet.enlarge (S := 𝒵) (zB.Z i) factor

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
