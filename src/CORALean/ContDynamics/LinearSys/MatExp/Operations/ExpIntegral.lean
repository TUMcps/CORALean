module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# The matrix exponential, integrated

`expIntegral`: [1, Eq. 7]'s `∫₀ᵗ e^{Aσ} dσ`, as the series `∑ᵢ Aⁱ t^{i+1}/(i+1)!`: `Matrix` carries
no metrizable-space instance Bochner integration can see, so `expIntegral_mulVec` ties it back to
the integral one vector at a time.

## Inputs
* `A` – system matrix
* `t` – time

## Output
* integral of the matrix exponential up to the time

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∫₀ᵗ e^{Aσ} dσ`, as the series `∑ᵢ Aⁱ t^{i+1}/(i+1)!`: `Matrix` carries no
metrizable-space instance Bochner integration can see, so `expIntegral_mulVec`
ties it back to the integral one vector at a time. -/
noncomputable def MatExp.expIntegral (A : Mat ℝ n n) (t : ℝ) : Mat ℝ n n :=
  ∑' i : ℕ, (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
