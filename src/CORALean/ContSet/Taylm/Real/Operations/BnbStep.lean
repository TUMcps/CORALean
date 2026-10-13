import CORALean.ContSet.Taylm.Real.Operations.ArgMaxIdx
import CORALean.ContSet.Taylm.Real.Operations.SplitAt

/-!
# One step of branch and bound

Lines 8-29 of [1, Alg. 1], for any way `bnd` of bounding a box: find the box whose interval holds
the upper bound and the one whose interval holds the lower bound; if they are one box, halve it,
otherwise halve each. The source's `α̅` and `α̲`; lines 15-16, 22-23 and 28-29 are `bnd` itself.

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

noncomputable def Taylm.bnbStep (bnd : (Fin n → ℝ × ℝ) → ℝ × ℝ) (l : List (Fin n → ℝ × ℝ)) :
    List (Fin n → ℝ × ℝ) :=
  -- 8: the box whose interval holds the upper bound
  let αhi := Taylm.argMaxIdx (l.map fun B => (bnd B).2)
  -- 9: the box whose interval holds the lower bound
  let αlo := Taylm.argMaxIdx (l.map fun B => -(bnd B).1)
  -- 10-16: one box holds both, and is halved; 17-29: each is halved
  if αhi = αlo then Taylm.splitAt αhi l else Taylm.splitAt αlo (Taylm.splitAt αhi l)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
