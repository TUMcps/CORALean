module

public import CORALean.ContSet.Taylm.Real.Operations.ReexpTerms
public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.reexpand`

CORA's `reexpand(obj, int)`: the model re-expanded at the centre of a sub-box `B` of the
normalized box and rescaled by its radius, so that the new variables again range over `[-1, 1]`;
the remainder is kept. The `reexp` of the advanced branch and bound of [1, Alg. 1].

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.reexpand (B : Fin n → Interval ℝ) (T : Taylm n) : Taylm n :=
  ⟨Taylm.reexpTerms (Taylm.boxMid B) (Taylm.boxRad B) T.terms, T.rem, T.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
