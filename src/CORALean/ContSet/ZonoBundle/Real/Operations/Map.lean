module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.map`

A linear map applied to every zonotope in the family [1, Prop. 1], the count `k` untouched:
`construct` reads only the family, so moving each member is all a bundle needs
to move.

## Inputs
* `f` – linear map
* `zB` – zonotope bundle

## Output
* the image under the map

## References

* [1] [M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.](../../../../../../references/2011/althoff-cdc-zonotope-bundles.md)
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.map (f : α →ₗ[ℝ] β) (zB : ZonoBundle α) : ZonoBundle β where
  k := zB.k
  Z := fun i => Zonotope.map f (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
