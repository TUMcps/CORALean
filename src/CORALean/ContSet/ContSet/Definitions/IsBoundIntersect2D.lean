module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# What the two-dimensional line intersection must return

`BOUND_INTERSECT_2D` of [1, Alg. 3] and [1, Alg. 4] takes a two-dimensional set `S` and the
line `L_γ = {(x, y) | x = γ}` and returns a segment `[m; M]` with `{γ} × [m; M] = S ∩ L_γ`, an
empty one (`m = ∞`, `M = −∞`) when they do not meet. `IsBoundIntersect2D bound` says that the
function `bound` does: `{y | (γ, y) ∈ S}` is `[m, M]` for every `S` and `γ`. It is what
[1, Alg. 2] asks of its subroutine: the specification of the scanning and of the dichotomic
search, not either algorithm.

## Inputs
* `bound` – candidate bound function

## Output
* `bound` returns exact slice bounds of every set at every abscissa

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output of [1]'s `BOUND_INTERSECT_2D` (Algorithms 3 and 4): `bound S γ = (m, M)` has
`{γ} × [m; M] = S ∩ L_γ`, for every `S` and `γ`. A specification, not an algorithm. -/
def ContSet.IsBoundIntersect2D (bound : Set (ℝ × ℝ) → ℝ → Real.Interval ℝ) : Prop :=
  ∀ (S : Set (ℝ × ℝ)) (γ : ℝ),
    {y : ℝ | (γ, y) ∈ S} = Set.Icc (bound S γ).inf (bound S γ).sup

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
