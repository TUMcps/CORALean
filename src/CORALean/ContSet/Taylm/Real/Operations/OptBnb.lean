import CORALean.ContSet.Taylm.Real.Operations.BranchAndBound

/-!
# `Taylm.optBnb`

CORA's `optBnb`: the bounds of a model's polynomial over the normalized box by branch and bound,
[1, Alg. 1] in its standard setting, plus the remainder. CORA's loop bounds each sub-box by
interval arithmetic, with the stopping test relative to the previous width; this one is the
source's listing, stopped by `fuel` when it does not settle.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.optBnb (T : Taylm n) (ε : ℝ) (fuel : ℕ) : ℝ × ℝ :=
  let b := Taylm.branchAndBound T.terms (fun _ => (-1, 1)) ε false fuel
  (b.1 + T.remInf, b.2 + T.remSup)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
