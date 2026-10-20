module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContSet.Interval.Real.Instances

@[expose] public section

/-!
# The adaptive input remainder `Δt · [-W, W]`

CORA's `errorSolution_adaptive`: `W = |e^{|A|Δt} − ∑ᵢ₌₀^η |A|ⁱΔtⁱ/i!|` entrywise,
`E = [-W, W]`, and what the orders past `η` of `∫₀^Δt e^{Aσ}dσ` can add is `E Δt`. The
entrywise `|A|` of [1, Lemma 1] replaces the norm series of `inputRemainder`.

## Inputs
* `A` – system matrix
* `Δt` – step length
* `η` – Taylor order

## Output
* interval matrix of the adaptive input remainder

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

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Δt · [-W, W]`, with `W = |E(Δt, η)|` read off `expRemainderMat` entry by entry. -/
noncomputable def MatExp.adaptiveRemainder (A : Mat ℝ n n) (Δt : ℝ) (η : ℕ) :
    Interval (Mat ℝ n n) where
  inf := fun j k => -(Δt * |MatExp.expRemainderMat A Δt η j k|)
  sup := fun j k => Δt * |MatExp.expRemainderMat A Δt η j k|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
