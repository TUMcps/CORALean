import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdaptiveRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff

/-!
# The integrated exponential as an interval matrix

CORA's `eAtInt = Asum + E Δt` of `errorSolution_adaptive`, where `Asum` is `Δt I` plus
`Aⁱ Δt^{i+1}/(i+1)!` for `i = 1, …, η` and `E Δt = [-ΔtW, ΔtW]`: the matrix a *static*
uncertain input is multiplied by, centred on the exact orders, the remainder being [1, Lemma 1]'s.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Asum + Δt [-W, W]`, with `Asum = ∑ᵢ₌₀^η Aⁱ Δt^{i+1}/(i+1)!`. -/
noncomputable def MatExp.adaptiveIntegral (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i) j k
    - (MatExp.adaptiveRemainder A Δt η).sup j k
  sup := fun j k => (∑ i ∈ Finset.range (η + 1), MatExp.particularCoeff A Δt i) j k
    + (MatExp.adaptiveRemainder A Δt η).sup j k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
