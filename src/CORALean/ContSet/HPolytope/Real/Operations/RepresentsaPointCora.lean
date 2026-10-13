import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.representsaPointCora`: the `'point'` test as CORA's code computes it

`@polytope/representsa_.m`, branch `'point'` (l. 68-70), for `n ≥ 2`:

```
[fulldim,subspace] = isFullDim(P);
res = ~fulldim && isempty(subspace);
```

`isFullDim` with two outputs, for an H-representation in `n ≥ 2` (`aux_isFullDim_nD_H_subspace`,
`@polytope/isFullDim.m`), starts with `if representsa_(P,'emptySet',tol)`, answering
`res = false; subspace = []`. A point has `fulldim = false` and `subspace = []` (the comment
"if P is just a point, subspace=[]"), so the empty polytope passes as a point. The rest of the
algorithm (a nonempty `P`) is not modelled and is taken as the given pair `rest`. Emptiness is
the set-level test. Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `res` for `representsa_(P, 'point')`, `n ≥ 2`, H-representation; `rest` is the
`isFullDim` pair of a nonempty `P`. -/
noncomputable def HPolytope.representsaPointCora (P : HPolytope (Fin n → ℝ))
    (rest : Bool × List (Fin n → ℝ)) : Bool :=
  -- [fulldim,subspace] = isFullDim(P)
  let r : Bool × List (Fin n → ℝ) := if P.construct = ∅ then (false, []) else rest
  !r.1 && r.2.isEmpty                  -- res = ~fulldim && isempty(subspace)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
