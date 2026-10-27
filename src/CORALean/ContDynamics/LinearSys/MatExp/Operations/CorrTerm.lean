module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeff
public import CORALean.Global.Tensor

@[expose] public section

/-!
# What one order contributes to the correction

`corrTerm`: what order `i` contributes to [1, Thm. 3]'s correction, at the far end of its range.
The interval it spans is between this and zero, on whichever side its sign puts it.

## Inputs
* `A` – system matrix
* `r` – step length
* `i` – order index
* `j` – row index
* `k` – column index

## Output
* contribution of the order to the correction entry

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What order `i` contributes to the correction, at the far end of its range.
The interval it spans is between this and zero, on whichever side its sign puts
it. -/
noncomputable def MatExp.corrTerm (A : Mat ℝ n n) (r : ℝ) (i : ℕ) (j k : Fin n) : ℝ :=
  MatExp.corrCoeff i * r ^ i * (((Nat.factorial i : ℝ))⁻¹ * (A ^ i) j k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
