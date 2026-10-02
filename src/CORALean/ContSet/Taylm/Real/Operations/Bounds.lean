import CORALean.ContSet.Taylm.Real.Operations.PolyBounds

/-!
# The range of a Taylor model

The polynomial's range plus the remainder: one coordinate of CORA's `interval`, which
`Conversion/Real/Taylm_to_Interval` assembles.
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
