import CORALean.Global.Tensor
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Where the state-dependent constant flow hits the guard

[1, Sec. 5.4]: `y_h(x₀) = x₀ + (Ax₀ + b)(d - nᵀx₀)/(nᵀ(Ax₀ + b))`, the point at which the
flow `ẏ = Ax₀ + b` of eq. (2) from `x₀` meets the hyperplane `nᵀx = d` — the function of the
initial state whose Taylor series [1, Prop. 3] encloses over a set of initial states, and
whose derivatives [1, Prop. 2] gives. `GuardMap.hitSet` adds the error set to it.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
