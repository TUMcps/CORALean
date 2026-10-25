module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The sum of a set and a segment

[1, Def. 1.3] builds a zonotope from the operation `A ⊕ x := convexhull(A ∪ (A + x))`, a
special case of the Minkowski sum: `A` swept along the segment from `0` to `x`. It is what
`Zonotope.generatorHull` iterates, one generator at a time (the paper's "evolution").

## Inputs
* `A` – set
* `x` – generator vector

## Output
* convex hull of `A` and `A + x`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 1.3]: `A ⊕ x = convexhull(A ∪ (A + x))`. -/
def Zonotope.segmentSum (A : Set (Vec ℝ n)) (x : Vec ℝ n) : Set (Vec ℝ n) :=
  convexHull ℝ (A ∪ (fun a => a + x) '' A)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
