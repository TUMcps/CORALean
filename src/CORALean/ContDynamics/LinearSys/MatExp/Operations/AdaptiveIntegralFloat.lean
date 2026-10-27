module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ParticularCoeffSumFloat

@[expose] public section

/-!
# The integrated exponential as a float interval matrix

`adaptiveIntegral` computed in `𝕋`: CORA's `eAtInt = Asum + E Δt` of
`errorSolution_adaptive`, `Asum` the float `particularCoeffSum` from order `0` and `E Δt`
the float `intervalInputRemainder`, which holds `Δt [-W, W]`
(`adaptiveRemainder_subset_intervalInputRemainder`). The remainder is [1, Lemma 1]'s.

## Inputs
* `A` – float interval matrix
* `Δt` – float step length
* `η` – Taylor order

## Output
* float interval matrix enclosing the integrated exponential

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Asum + E Δt`, `Asum = Σᵢ₌₀^η [Aⁱ Δt^{i+1}/(i+1)!]`, over the box `A`. -/
def MatExp.adaptiveIntegral (A : Interval (Mat 𝕋 n n)) (Δt : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let Asum := MatExp.particularCoeffSum A Δt 0 η                      -- Σᵢ Aⁱ Δt^{i+1}/(i+1)!
  let EΔt := MatExp.intervalInputRemainder A Δt η                     -- ⊇ Δt [-W, W]
  (Interval.matPlus Asum EΔt).materialiseMat                          -- Asum + E Δt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
