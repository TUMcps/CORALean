module

public import CORALean.ContSet.VPolytope.Real.VPolytope
public import CORALean.ContSet.VPolytope.Real.Operations.DistPoint
public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# `VPolytope.hausdorffDist`

CORA's `polytope/hausdorffDist` between two bounded nonempty polytopes: the largest distance from a
vertex of either polytope to the other one, the distance of a vertex `x` to `S` being
`aux_distPolyPoint`, `sqrt(val + x'x)` with `val` the optimum of the quadratic program `min y'y -
2x'y` over `y ∈ S`.

The vertices are `P.V`: CORA takes `vertices(P)`, the extreme points, and the stored vertices are
CORA's when they are the extreme points. The empty and unbounded cases (`Inf`, or `0` for two empty
sets) are not here: a `VPolytope` is bounded, and `k = 0` denotes `∅`.

## Inputs
* `P` – first polytope
* `S` – second polytope

## Output
* largest distance from a vertex of either polytope to the other
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def VPolytope.hausdorffDist (P S : VPolytope (Vec ℝ n)) : ℝ :=
  -- `val = 0`
  let val₀ : ℝ := 0
  -- `for i = 1:size(V_P,2): val = max(val, aux_distPolyPoint(S, V_P(:,i)))`
  let valP : ℝ := (List.finRange P.k).foldl
    (fun val i => max val (VPolytope.distPoint S.construct (P.V i))) val₀
  -- `for i = 1:size(V_S,2): val = max(val, aux_distPolyPoint(P, V_S(:,i)))`
  (List.finRange S.k).foldl
    (fun val i => max val (VPolytope.distPoint P.construct (S.V i))) valP

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
