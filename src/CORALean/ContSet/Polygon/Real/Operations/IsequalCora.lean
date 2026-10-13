module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `Polygon.isequalCora`: `polygon/isequal` as CORA's code computes it

CORA's `@polygon/isequal.m` (l. 1-76) compares the boundary vertex lists of two polygons
(after `removeCollinearPoints`, taken here as given): equal numbers of vertices, then every
position `idx` in `V2` that holds `V1(1,:)` is tried as the start of a cyclic re-ordering of `V2`,
and the lists are compared in order. The loop (l. 64-71) reads

```
for i = 1:length(idx)
    V2_ = [V2(idx:end, :); V2(1:idx-1, :)];
```

with `idx`, not `idx(i)`. MATLAB's colon operator takes the first element of a vector operand,
so every pass re-orders `V2` from `idx(1)`. A boundary that visits one point twice has several
such positions, and only the first is ever tried. The lists are `List`s of vertices (rows of
`V1`, `V2`); `withinTol(a,b,tol)` is its absolute branch `|a - b| <= tol` (the relative branch is
only wider); `compareMatrices(..., tol, 'equal', true)` with equal sizes is `all(withinTol(…))`.
Read from the source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `res` for `isequal(pgon1, pgon2, tol)`, from the vertex lists `V1`, `V2`. -/
noncomputable def Polygon.isequalCora (tol : ℝ) (V1 V2 : List (Vec ℝ 2)) : Bool :=
  -- l. 43: both empty -> `res = true`
  if V1 = [] ∧ V2 = [] then true
  -- l. 49: different numbers of vertices -> `res = false`
  else if V1.length ≠ V2.length then false
  else
    -- l. 56: `idx = find(all(withinTol(V1(1,:), V2, tol), 2))`, as 0-based positions
    let idx : List ℕ := (List.range V2.length).filter fun j =>
      (decide (|V1.head! 0 - V2[j]! 0| ≤ tol ∧ |V1.head! 1 - V2[j]! 1| ≤ tol))
    -- l. 59: `isempty(idx)` -> `res = false`
    if idx = [] then false
    else
      -- l. 64: `for i = 1:length(idx)`: the start is `idx`, which MATLAB's colon reads as `idx(1)`
      idx.any fun _ =>
        -- l. 66: `V2_ = [V2(idx:end, :); V2(1:idx-1, :)]`
        let V2_ := V2.drop idx.head! ++ V2.take idx.head!
        -- l. 68: `compareMatrices(V1, V2_, tol, 'equal', true)`
        (decide (List.Forall₂ (fun a b => |a 0 - b 0| ≤ tol ∧ |a 1 - b 1| ≤ tol) V1 V2_))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
