module

public import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound

@[expose] public section

/-!
# `Taylm.optBnbAdv`

CORA's `optBnbAdv`: the bounds of a model's polynomial over the normalized box by branch and
bound, [1, Alg. 1] in its advanced setting, plus the remainder. CORA's loop re-expands the model
at each sub-box's centre first, and stops on an absolute change of `2ε`; this one is the
source's listing, stopped by `fuel` when it does not settle.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.optBnbAdv (T : Taylm n) (ε : ℝ) (fuel : ℕ) : ℝ × ℝ :=
  let b := Taylm.branchAndBound T.terms (fun _ => (-1, 1)) ε true fuel
  (b.1 + T.remInf, b.2 + T.remSup)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
