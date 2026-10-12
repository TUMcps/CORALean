import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.Global.EuclideanNorm

/-!
# `Zonotope.cloud2zonotopeCompress`

[1, Alg. 4] (`compress`): clamp each point's coordinate along `u = g / ‖g‖` to `[-‖g‖, ‖g‖]` and
subtract it, so the cloud shrinks along `g` by at most the segment `[-1, 1] g` (`(43)`, proved as
`cloud2zonotopeCompress_mem`). The points are the columns of the matrix the paper calls `X`.

At `g = 0` step 2 reads `0 / 0`, which the paper leaves undefined and Lean's `x / 0 = 0` makes
`u = 0`: every point is returned unchanged.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {κ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X = compress(X, g)`, [1, Alg. 4]. -/
noncomputable def Zonotope.cloud2zonotopeCompress (X : κ → Vec ℝ n) (g : Vec ℝ n) :
    κ → Vec ℝ n :=
  let u := (‖g‖₂)⁻¹ • g
  fun j =>
    let d := X j ⬝ᵥ u
    let d := min ‖g‖₂ (max (-‖g‖₂) d)
    X j - d • u

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
