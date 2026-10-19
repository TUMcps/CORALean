module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Pi

@[expose] public section

/-!
# `VPolytope.plusPruneCora`: the hull step of `plus` for matrix polytopes, as CORA's code runs it

`@matPolytope/plus.m` (l. 36-60) adds two `n × m` matrix polytopes with `h1` and `h2` vertices: it
stacks all `h1·h2` sums as columns of `vecVpot`, an `(n·m) × (h1·h2)` array, then prunes them to the
hull vertices with `K = convhulln(vecVpot, opt); vecV = vecVpot(K,:);` (l. 55, 58). `convhulln`
takes one point per *row*, and `vecVpot` has one vertex per *column* (every other CORA call passes
`V'`). So the points are the `n·m` entries, in dimension `h1·h2`; for `n·m <= h1·h2` `convhulln`
throws and the `try` keeps all vertices, correctly. For `n·m > h1·h2` it succeeds, `K` holds indices
of *entries*, and the result is not the polytope of the sum vertices. Modelled: `vecVpot` as its
rows and `K` as a list of facets, `K(:)` read column by column. Read from the source, not run; Qhull
through scipy returns for the example below four matrices, none of them `A` or `B`.

# CORA's `plus` of two matrix polytopes returns wrong vertices

`A = [0 1; 1 0]`, `B = [0 1; 0 1]`, `matPolytope(cat(3,A,B)) + matPolytope(zeros(2,2))` has the sum
vertices `A` and `B` and gets four matrices, not all on the line through `A` and `B`, whatever order
and orientation `convhulln` returns the four edges of the square of entry pairs in.

## Inputs
* `σ` – order of the four edges
* `o` – orientation of the four edges

## Hypotheses
* none

## Conclusion
* the pruned sum is not the polytope of the sum vertices
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- Lines 55-60 of `@matPolytope/plus.m`: `K = convhulln(vecVpot)`, `vecV = vecVpot(K,:)`,
`matV = reshape(vecV, n, m, [])`, on the `n·m` rows `vecVpot` of `d` columns and the facet list `K`
that `convhulln` returned. Each matrix of the result is its entries, column by column. -/
def VPolytope.plusPruneCora (n m d : ℕ) (vecVpot : List (List ℤ)) (K : List (List ℕ)) :
    List (List ℤ) :=
  let Kcol := (List.range d).flatMap fun c => K.map fun f => f.getD c 0     -- K(:)
  let vecV := Kcol.map fun i => vecVpot.getD i []                           -- vecVpot(K,:)
  let vecVcol := (List.range d).flatMap fun c => vecV.map fun r => r.getD c 0  -- vecV(:)
  (List.range (vecVcol.length / (n * m))).map fun j =>                      -- reshape(·,n,m,[])
    (List.range (n * m)).map fun i => vecVcol.getD (n * m * j + i) 0


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The example: `A = [0 1; 1 0]` and `B = [0 1; 0 1]` plus the zero matrix; the row of entry `k`
is `(A_k, B_k)` (entries column by column). -/
def VPolytope.aux_squareRows : List (List ℤ) := [[0, 0], [1, 0], [1, 1], [0, 1]]

/-- Whether a matrix lies on the line through `A` and `B` (flattened column by column): its
entries satisfy the three equations that hold for both. -/
def VPolytope.aux_onLineAB (M : List ℤ) : Bool :=
  M.getD 0 0 = 0 && M.getD 2 0 = 1 && M.getD 1 0 + M.getD 3 0 = 1

/-- The facets `convhulln` returns for the four points of the square: its four edges `{j, j+1}`,
each oriented as `o` says, listed in the order `σ`. -/
def VPolytope.aux_squareFacets (σ : Equiv.Perm (Fin 4)) (o : Fin 4 → Bool) : List (List ℕ) :=
  (List.finRange 4).map fun i =>
    if o i then [(σ i).val, ((σ i).val + 1) % 4] else [((σ i).val + 1) % 4, (σ i).val]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Whatever the order and orientation of the four edges, not every matrix of the result is on
the line through `A` and `B`, so the result is not the polytope of the sum vertices `A`, `B`. -/
theorem VPolytope.plusPrune_cora_counterexample (σ : Equiv.Perm (Fin 4)) (o : Fin 4 → Bool) :
    (VPolytope.plusPruneCora 2 2 2 VPolytope.aux_squareRows (VPolytope.aux_squareFacets σ o)).all
      VPolytope.aux_onLineAB = false := by
  revert σ o
  exact of_decide_eq_true rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
