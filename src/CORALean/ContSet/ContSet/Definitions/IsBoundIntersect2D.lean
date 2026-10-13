import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# What the two-dimensional line intersection must return

`BOUND_INTERSECT_2D` of [1, Alg. 3] and [1, Alg. 4] takes a two-dimensional set `S` and the
line `L_γ = {(x, y) | x = γ}` and returns a segment `[m; M]` with `{γ} × [m; M] = S ∩ L_γ`, an
empty one (`m = ∞`, `M = −∞`) when they do not meet. `IsBoundIntersect2D bound` says that the
function `bound` does: `{y | (γ, y) ∈ S}` is `[m, M]` for every `S` and `γ`. It is what
[1, Alg. 2] asks of its subroutine: the specification of the scanning and of the dichotomic
search, not either algorithm.

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 3]: `bound S γ = (m, M)` has `{γ} × [m; M] = S ∩ L_γ`, for every `S` and `γ`. -/
def ContSet.IsBoundIntersect2D (bound : Set (ℝ × ℝ) → ℝ → ℝ × ℝ) : Prop :=
  ∀ (S : Set (ℝ × ℝ)) (γ : ℝ),
    {y : ℝ | (γ, y) ∈ S} = Set.Icc (bound S γ).1 (bound S γ).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
