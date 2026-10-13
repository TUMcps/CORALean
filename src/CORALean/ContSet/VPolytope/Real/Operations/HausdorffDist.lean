import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.VPolytope.Real.Operations.DistPoint
import CORALean.Global.EuclideanHausdorffDist

/-!
# `VPolytope.hausdorffDist`

CORA's `polytope/hausdorffDist` between two bounded nonempty polytopes: the largest
distance from a vertex of either polytope to the other one, the distance of a vertex `x` to a
polytope `S` being `aux_distPolyPoint`, `sqrt(val + x'x)` with `val` the optimal value of the
quadratic program `min y'y - 2x'y` over `y ∈ S`. The loop over the vertices of the first
polytope and then of the second starts at `val = 0`.

The vertices are `P.V`: for a polytope given by constraints CORA takes `vertices(P)`, the
extreme points, whose hull is the polytope; here, as for `VPolytope.center`, the stored
vertices are CORA's when they are the extreme points. The empty and unbounded cases (`Inf`,
or `0` for two empty sets) are not here: a `VPolytope` is bounded, and `k = 0` denotes `∅`.
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
