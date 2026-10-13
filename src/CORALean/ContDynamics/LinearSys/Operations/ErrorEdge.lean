module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeff
public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# The generator sums of the error solution

CORA's `RerrorInt_etanoF`: `sum(abs(generators(AVsum)),2)` after the terms up to order
`η` are added, the row sums of the absolute values of the generators `Aⁱ Δt^{i+1}/(i+1)! G`
of `⊕ᵢ₌₀^η Aⁱ Δt^{i+1}/(i+1)! V`, the terms of [1, Prop. 11].

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The edge length of the generator sum, per coordinate, up to order `η`. -/
noncomputable def LinearSys.errorEdge (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (V : Zonotope (Vec ℝ n)) (η : ℕ) : Vec ℝ n :=
  fun d => ∑ i ∈ Finset.range (η + 1), ∑ j, |(MatExp.particularCoeff (toRealMat sys.A) Δt i
    *ᵥ V.G j) d|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
