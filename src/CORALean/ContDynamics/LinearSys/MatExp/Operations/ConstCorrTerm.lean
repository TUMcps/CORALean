module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.Global.Tensor

@[expose] public section

/-!
# What one order contributes to the integrated correction

`constCorrTerm`: [1, Sec. III-A]'s order `i+2` contribution to the *integrated* correction. The same
shape as `corrTerm`, one factorial further along and one matrix power back, which is what
integrating each order of the exponential does to it.

## Inputs
* `A` – system matrix
* `r` – step length
* `i` – order index
* `j` – row index
* `k` – column index

## Output
* contribution of the order to the integrated correction entry

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

/-- What order `i+2` contributes to the *integrated* correction. The same shape
as `corrTerm`, one factorial further along and one matrix power back, which is
what integrating each order of the exponential does to it. -/
noncomputable def MatExp.constCorrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) :
    ℝ :=
  MatExp.corrCoeff (i + 2) * r ^ (i + 2)
    * (((Nat.factorial (i + 2) : ℝ))⁻¹ * (A ^ (i + 1)) j k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
