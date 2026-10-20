module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.Zip

@[expose] public section

/-!
# `Polygon.randPointExtremeCora`: `randPoint(pgon, 'all', 'extreme')` as CORA's code selects

`@polygon/randPoint_.m`, `aux_randPointExtreme` (l. 77), drops the NaN columns of the vertex
matrix `V` (2 x k) by

```
V = V(:,~any(isnan(V),2));
```

`any(isnan(V),2)` has one entry per row, so the mask has length 2, and a logical index shorter
than the matrix keeps only the first two columns it flags: for a polygon without NaN the mask is
`[1;1]` and `V` keeps columns 1 and 2, for one with a NaN column (a hole) it is `[0;0]` and `V` is
empty. `any(isnan(V),1)` was meant. `N = 'all'` returns `V`. A column is `none` when it holds NaN.
Read from the source, not run.

# CORA's `randPoint` of the unit square with `'all'` and `'extreme'` returns two vertices

`randPoint(polygon([0 1 1 0],[0 0 1 1]), 'all', 'extreme')` returns `(0,0)` and `(1,0)`; the
vertices `(1,1)` and `(0,1)` are missing.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the unit square keeps its first two vertices; a polygon with a NaN column keeps none
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `p` for `N = 'all'`: the columns `j` of `V` with `j < length(mask)` and `mask(j)`,
for the mask `~any(isnan(V),2)` of one entry per row (two rows). -/
def Polygon.randPointExtremeAllCora (V : List (Option (Fin 2 → ℝ))) : List (Option (Fin 2 → ℝ)) :=
  -- ~any(isnan(V),2): every row has a NaN as soon as one column does
  let mask : List Bool := List.replicate 2 (!V.any Option.isNone)
  -- V(:,mask): a logical index over the first `length mask` columns
  ((V.zip mask).filter (fun c => c.2)).map (fun c => c.1)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unit square keeps its first two vertices; a polygon with a NaN column keeps none. -/
theorem Polygon.randPointExtremeAll_cora_counterexample : -- --- CONCL ---
    Polygon.randPointExtremeAllCora
        [some ![0, 0], some ![1, 0], some ![1, 1], some ![0, 1]] =
      [some ![0, 0], some ![1, 0]] ∧
    Polygon.randPointExtremeAllCora
        [some ![0, 0], some ![1, 0], some ![1, 1], none, some ![0, 1]] = [] := by -- --- PROOF ---
  constructor <;> simp [Polygon.randPointExtremeAllCora]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
