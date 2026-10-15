module

public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

@[expose] public section

/-!
# The range of a Taylor model

The polynomial's range plus the remainder: one coordinate of CORA's `interval`, which
`Conversion/Real/Operations/Taylm_to_Interval` assembles.

The bound `B(T) = B(P) + [I]` of [1, Eq. 5], `B(P)` being interval evaluation over the
normalized box.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bounds (T : Taylm n) : Interval ℝ :=
  ⟨(Taylm.polyBounds T.terms).inf + T.rem.inf, (Taylm.polyBounds T.terms).sup + T.rem.sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
