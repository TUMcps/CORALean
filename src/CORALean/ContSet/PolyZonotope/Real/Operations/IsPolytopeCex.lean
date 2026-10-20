module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `PolyZonotope.isPolytopeCex`

`{(2a + b, a c) | a, b, c ∈ [-1, 1]}`: `c = 0`, `G = [(2,0), (1,0), (0,1)]`, monomials `a`,
`b`, `a c`. It is not convex (`isPolytopeCex_not_convex`), yet CORA's `isPolytope` [1] says `true`.
Hand trace, factors `(a, b, c)`: all exponents are `0/1`, so `any(expMat >= 2)` does not fire;
`aux_polyVertices`: the corner images are distinct and `convhulln` keeps the extreme points
`(±3, ±1)`, from `I = (1,1,1), (1,1,-1), (-1,-1,-1), (-1,-1,1)`; `aux_normalCone` at `I` gives
the columns `(-2a, -ac)`, `(-b, 0)`, `(0, -ac)`, which at the four extreme points span the four
quadrants and contain the other three vertices: every `aux_inCone` LP has slack `0`, so `true`.

## Inputs
* none

## Output
* the polynomial zonotope of the polytope counterexample

## References

* [1] `contSet/@polyZonotope/isPolytope.m`, CORA (Sep. 2025), by N. Kochdumper (2019).
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `{(2a + b, a c) | a, b, c ∈ [-1, 1]}`, factors `(a, b, c)`. -/
def PolyZonotope.isPolytopeCex : PolyZonotope (Vec ℝ 2) where
  p := 3
  h := 3
  q := 0
  c := 0
  G := ![(![2, 0] : Vec ℝ 2), ![1, 0], ![0, 1]]
  E := ![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]]
  GI := Fin.elim0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
