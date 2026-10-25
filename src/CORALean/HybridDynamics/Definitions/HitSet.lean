module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# The set eq. (15) of [1] puts a guard hit in, from one initial state

[1, Eq. 15]: under the state-dependent constant flow `ẏ = Ax₀ + b` of eq. (2), with the
linear system's state within `E` of it, eq. (14), the hyperplane `nᵀx = d` is hit in
`R_h(x₀) = y_h(x₀) ⊕ R_{h,E}(x₀)`: `y_h(x₀) = x₀ + (Ax₀ + b)(d - nᵀx₀)/(nᵀ(Ax₀ + b))` is the flow's
own hit and `R_{h,E}(x₀) = (Ax₀ + b)(-nᵀE)/(nᵀ(Ax₀ + b)) ⊕ E` what `E` adds, as the paper
splits it. Eq. (1) with `b` replaced by `Ax₀ + b`, the paper's own reading.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `E` – flow error set
* `x₀` – initial state

## Output
* set the guard hit lies in

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 15]: `R_h(x₀) = y_h(x₀) ⊕ R_{h,E}(x₀)`. -/
def GuardMap.hitSet (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (E : Set (Vec ℝ n)) (x₀ : Vec ℝ n) :
    Set (Vec ℝ n) :=
  let f₀ : Vec ℝ n := A *ᵥ x₀ + b                                    -- `Ax₀ + b`
  let yh : Vec ℝ n := x₀ + ((d - nv ⬝ᵥ x₀) / (nv ⬝ᵥ f₀)) • f₀       -- `y_h(x₀)`
  let RhE : Set (Vec ℝ n) := (fun e => (-(nv ⬝ᵥ e) / (nv ⬝ᵥ f₀)) • f₀) '' E + E  -- `R_{h,E}(x₀)`
  {yh} + RhE

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
