module

public import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound

@[expose] public section

/-!
# `Taylm.optBnb`

CORA's `optBnb`: the bounds of a model's polynomial over the normalized box by branch and bound,
[1, Alg. 1] in its standard setting, plus the remainder. CORA's loop bounds each sub-box by
interval arithmetic, with the stopping test relative to the previous width; this one is the
source's listing, stopped by `fuel` when it does not settle.

## Inputs
* `T` – Taylor model
* `ε` – tolerance
* `fuel` – step budget

## Output
* enclosure of its range by branch and bound

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.optBnb (T : Taylm n) (ε : ℝ) (fuel : ℕ) : Interval ℝ :=
  let b := Taylm.branchAndBound T.terms (fun _ => ⟨-1, 1⟩) ε false fuel
  ⟨b.inf + T.rem.inf, b.sup + T.rem.sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
