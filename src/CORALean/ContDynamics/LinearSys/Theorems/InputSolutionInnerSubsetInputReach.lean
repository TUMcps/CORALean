import CORALean.ContDynamics.LinearSys.Operations.InputSolutionInner
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemInputReach

/-!
# The inner approximation really is one

The inner approximation of [1, Prop. 1] is one because `A⁻¹(e^{AΔt} - I)s` is what the
*constant* input `s` contributes over the step, and a constant input is
admissible: `expIntegral_mem_inputReach` is that observation, and this is it
read over the whole set.

The half of [1, Prop. 1] that needs no estimate at all — and the half that makes
the proposition's Hausdorff bound one-sided, the exact solution being enclosed
between the two approximations.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: the set constant inputs reach is inside the particular
solution. -/
theorem LinearSys.inputSolutionInner_subset_inputReach (sys : LinearSys 𝕋 n) {U : S n}
    {Δt : ℝ} (hΔt : 0 ≤ Δt) :
    sys.inputSolutionInner U Δt ⊆ sys.inputReach U Δt := by
  rintro _ ⟨s, hs, rfl⟩
  exact sys.expIntegral_mem_inputReach hΔt hs

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
