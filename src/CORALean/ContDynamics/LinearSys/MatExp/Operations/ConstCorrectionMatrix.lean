module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrTerm
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# The integrated correction matrix

`constCorrectionMatrix`: the `F̃` of [1, Sec. III-A], formed without an inverse of `A`: orders
`1` through `η` of `∫₀ᵗ e^{Aσ}dσ - (t/r)∫₀ʳ e^{Aσ}dσ` exactly, and everything past `η` in
`E(r)·r`, integrating the exponential's tail scaling it by at most the step. [1] bounds that
tail by `W(r)r` instead, `W` the entrywise tail of `e^{|A|r}`.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order

## Output
* interval matrix of the integrated correction

## References

* [1] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `F̃` of [1, Sec. III-A], without an inverse of `A`: orders `1` through `η` of
`∫₀ᵗ e^{Aσ}dσ - (t/r)∫₀ʳ e^{Aσ}dσ` exactly, and everything past `η` in `E(r)·r`,
integrating the exponential's tail scaling it by at most the step. -/
noncomputable def MatExp.constCorrectionMatrix (A : Mat ℝ n n) (r : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => (∑ i ∈ Finset.range η, min (MatExp.constCorrTerm A r i j k) 0)
    - r * MatExp.expRemainderBound (r • A) η
  sup := fun j k => (∑ i ∈ Finset.range η, max (MatExp.constCorrTerm A r i j k) 0)
    + r * MatExp.expRemainderBound (r • A) η

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
