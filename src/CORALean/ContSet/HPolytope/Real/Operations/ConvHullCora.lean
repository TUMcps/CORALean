import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.convHullCora`: `convHull_` as CORA's code computes it

`@polytope/convHull_.m` comments "convex hull with empty set is other set" (l. 63) and then
returns `polytope.empty(n)` when either operand represents the empty set (l. 64-67). Next the
fullspace exits (l. 70-76), then the 1-D and vertex-based computations (l. 79-97), which are a
parameter here (`rest`, not modelled). `representsa_(·, 'emptySet', eps)` reads as exact
emptiness. Read from the source, not run.

## References

* [1] `contSet/@polytope/convHull_.m`, CORA, ll. 60-97.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set [1] returns for two polytopes: the empty and fullspace exits, then `rest`. -/
noncomputable def HPolytope.convHullCora (P S : HPolytope (Vec ℝ n)) (rest : Set (Vec ℝ n)) :
    Set (Vec ℝ n) :=
  open Classical in
  -- l. 64-67: either operand `representsa_(·,'emptySet',eps)`, `P_out = polytope.empty(n)`
  if P.construct = ∅ ∨ S.construct = ∅ then ∅
  -- l. 70-76: either operand the fullspace, `P_out = polytope.Inf(n)`
  else if P.construct = Set.univ ∨ S.construct = Set.univ then Set.univ
  -- l. 79-97: the 1-D and vertex-based hulls (not modelled)
  else rest

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
