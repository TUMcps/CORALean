module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Where the state-dependent constant flow hits the guard

[1, Sec. 5.4]: `y_h(x₀) = x₀ + (Ax₀ + b)(d - nᵀx₀)/(nᵀ(Ax₀ + b))`, the point at which the
flow `ẏ = Ax₀ + b` of eq. (2) from `x₀` meets the hyperplane `nᵀx = d` — the function of the
initial state whose Taylor series [1, Prop. 3] encloses over a set of initial states, and
whose derivatives [1, Prop. 2] gives. `GuardMap.hitSet` adds the error set to it.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `x₀` – initial state

## Output
* point where the flow meets the guard

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `y_h(x₀) = x₀ + (Ax₀ + b)(d - nᵀx₀)/(nᵀ(Ax₀ + b))`. -/
noncomputable def GuardMap.hitPoint (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (x₀ : Vec ℝ n) :
    Vec ℝ n :=
  x₀ + ((d - nv ⬝ᵥ x₀) / (nv ⬝ᵥ (A *ᵥ x₀ + b))) • (A *ᵥ x₀ + b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
