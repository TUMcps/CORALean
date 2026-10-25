module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Taylm.qfbSearchStep`

[1, Sec. 3 (search for x₀)]: "`x₀` can be determined inexpensively by an iterative scheme to search
a series of `x₀⁽ⁱ⁾` in the direction of `-∇P₂` while limiting `x₀⁽ⁱ⁾` to stay inside `D`". One step
of it, on the domain box `D = [-1, 1]ⁿ` of a Taylor model: a step of length `α` along `-∇P₂`,
`∇P₂(x) = g + Hx` for `P₂ = c + g ⬝ x + ½ x ⬝ Hx` with `H` symmetric, then every coordinate limited
to `[-1, 1]`. The series is the iterate `x₀⁽ⁱ⁾ = step^[i] x₀⁽⁰⁾`.

## Inputs
* `H` – Hessian matrix
* `g` – gradient
* `α` – step length
* `x` – current point

## Output
* point after one step along the negative gradient, kept in the unit box

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3 (search for x₀)]: one step of the search for `x₀`, step length `α`. -/
noncomputable def Taylm.qfbSearchStep (H : Mat ℝ n n) (g : Vec ℝ n) (α : ℝ) (x : Vec ℝ n) :
    Vec ℝ n :=
  let grad := g + H *ᵥ x                                      -- ∇P₂(x)
  let y := x - α • grad                                       -- in the direction of −∇P₂
  fun k => max (-1) (min 1 (y k))                             -- limited to stay inside D

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
