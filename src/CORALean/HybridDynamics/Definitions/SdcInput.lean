module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# The constant flow [1, Prop. 1] chooses

[1, Prop. 1]: `b = Θ(t̃_h)x₀ + Γ*(t̃_h)u_c`, `Θ(t) = Σᵢ₌₂^η Aⁱtⁱ⁻¹/i!` and
`Γ*(t) = Σᵢ₌₀^η Aⁱtⁱ/(i + 1)!`, the vector `b` that makes the state-dependent constant flow
`y₀ + (Ay₀ + b)t` of eq. (3) meet the linear system `ẋ = Ax + u_c` at `t̃_h`, up to the
truncation at `η`. One `let` per printed matrix; `t` is the paper's `t̃_h`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
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

/-- [1, Prop. 1]: `b = Θ(t)x₀ + Γ*(t)u_c`. -/
noncomputable def GuardMap.sdcInput (A : Mat ℝ n n) (uc : Vec ℝ n) (t : ℝ) (η : ℕ)
    (x₀ : Vec ℝ n) : Vec ℝ n :=
  let Θ : Mat ℝ n n := ∑ i ∈ Finset.Ico 2 (η + 1), (t ^ (i - 1) / (i.factorial : ℝ)) • A ^ i
  let Γstar : Mat ℝ n n := ∑ i ∈ Finset.range (η + 1), (t ^ i / ((i + 1).factorial : ℝ)) • A ^ i
  Θ *ᵥ x₀ + Γstar *ᵥ uc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
