module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `Zonotope.cloud2zonotopeCompress`

[1, Alg. 4] (`compress`): clamp each point's coordinate along `u = g / ‖g‖` to `[-‖g‖, ‖g‖]` and
subtract it, so the cloud shrinks along `g` by at most the segment `[-1, 1] g` (`(43)`, proved as
`cloud2zonotopeCompress_mem`). The points are the columns of the matrix the paper calls `X`.

At `g = 0` step 2 reads `0 / 0`, which the paper leaves undefined and Lean's `x / 0 = 0` makes
`u = 0`: every point is returned unchanged.

## Inputs
* `X` – point cloud
* `g` – direction to compress along

## Output
* compressed point cloud

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on Automatic
      Control, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ} {κ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X = compress(X, g)`, [1, Alg. 4]. -/
noncomputable def Zonotope.cloud2zonotopeCompress (X : κ → Vec ℝ n) (g : Vec ℝ n) :
    κ → Vec ℝ n :=
  -- 2. compute the compression direction, `u = g / ‖g‖`
  let u := (‖g‖₂)⁻¹ • g
  -- 3. for each point-vector `xᵢ` in `X`
  fun j =>
    -- 4. compute its coordinate along `u`, `d := xᵢ · u`
    let d := X j ⬝ᵥ u
    -- 5. compress along `u`, `d := min(‖g‖, max(-‖g‖, d))`
    let d := min ‖g‖₂ (max (-‖g‖₂) d)
    -- 6. update the coordinates, `xᵢ = xᵢ - d u`
    X j - d • u

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
