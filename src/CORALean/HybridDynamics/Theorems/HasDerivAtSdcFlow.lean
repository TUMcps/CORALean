module

public import CORALean.HybridDynamics.Operations.SdcFlow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# `y₀ + (Ay₀ + b)t` solves `ẏ = Ay₀ + b`

[1, Eq. 3]: the derivative of an affine function of `t` is its slope, and at `t = 0` it
is `y₀`.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `y₀` – initial state
* `t` – time

## Hypotheses
* none

## Conclusion
* the flow starts at the state and has the constant slope

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3]: `sdcFlow A b y₀` starts at `y₀` and has slope `Ay₀ + b` everywhere. -/
theorem GuardMap.hasDerivAt_sdcFlow (A : Mat ℝ n n) (b y₀ : Vec ℝ n) (t : ℝ) :
    GuardMap.sdcFlow A b y₀ 0 = y₀ ∧
      HasDerivAt (GuardMap.sdcFlow A b y₀) (A *ᵥ y₀ + b) t := by
  refine ⟨by simp [GuardMap.sdcFlow], ?_⟩
  have h := ((hasDerivAt_id t).smul_const (A *ᵥ y₀ + b)).const_add y₀
  simp only [one_smul] at h
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
