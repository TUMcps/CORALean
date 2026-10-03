import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

/-!
# The range of a Taylor model

The polynomial's range plus the remainder: one coordinate of CORA's `interval`, which
`Conversion/Real/Taylm_to_Interval` assembles.

The bound `B(T) = B(P) + [I]` of [1, Eq. 5], `B(P)` being interval evaluation over the
normalized box.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.bounds (T : Taylm n) : ℝ × ℝ :=
  ((Taylm.polyBounds T.terms).1 + T.remInf, (Taylm.polyBounds T.terms).2 + T.remSup)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
