module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope

@[expose] public section

/-!
# `ZonoBundle.mtimesMatZonotope`

CORA's `matZonotope * zonoBundle` [1, Eq. (10)]: the same `k`, each component
multiplied on its own, exactly as `mtimes` does for a point matrix.

An enclosure twice over, and only the first reason is `mtimes`'s: an
intersection maps into the intersection of the images, and on top of that
`Zonotope.mtimesMatZonotope` already loosens each cross coefficient. The same
matrix is used in every component, but nothing here records that — each
component encloses on its own, so a correlation across components is lost.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ZonoBundle.mtimesMatZonotope (M : Zonotope (Mat ℝ m n))
    (zB : ZonoBundle (Vec ℝ n)) : ZonoBundle (Vec ℝ m) where
  k := zB.k
  Z := fun i => Zonotope.mtimesMatZonotope M (zB.Z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
