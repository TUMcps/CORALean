module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InputRemainder
public import CORALean.ContDynamics.LinearSys.Operations.InputTerm

@[expose] public section

/-!
# The outer approximation of the particular solution over one step, as a set

`LinearSys.inputSolution` is the same expression built out of `Plus` and
`Mtimes`, which only ever over-approximate, so what it denotes admits no upper
bound at all. [1, Prop. 1] measures a *distance* to this set, and a distance
needs both bounds — hence the Minkowski sum and the interval-matrix product
written out, which is what the paper's own `⊕ᵢ AⁱΔt^{i+1}/(i+1)! S ⊕ EΔt S` says.

The remainder factor is `MatExp.inputRemainder`, already `E` scaled by the step.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar Pointwise

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The orders up to `η` exactly, and the rest inside the interval matrix. -/
noncomputable def LinearSys.inputSolutionSet (sys : LinearSys 𝕋 n) (U : S n) (Δt : ℝ) (η : ℕ) :
    Set (Vec ℝ n) :=
  (∑ i ∈ Finset.range (η + 1), (fun s => sys.inputTerm Δt i *ᵥ s) '' construct U)
    + ⋃ M ∈ (MatExp.inputRemainder (toRealMat sys.A) Δt η).construct,
        (fun s => M *ᵥ s) '' construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
