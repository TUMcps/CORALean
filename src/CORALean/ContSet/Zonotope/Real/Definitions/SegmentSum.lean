import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The sum of a set and a segment

[1, Def. 1.3] builds a zonotope from the operation `A ⊕ x := convexhull(A ∪ (A + x))`, a
special case of the Minkowski sum: `A` swept along the segment from `0` to `x`. It is what
`Zonotope.generatorHull` iterates, one generator at a time (the paper's "evolution").

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
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
