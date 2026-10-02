import CORALean.ContSet.Taylm.Real.Taylm

/-!
# `Taylm.uminus`

CORA's unary `-`: every coefficient negated, the remainder reflected.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.uminus (T : Taylm n) : Taylm n :=
  ⟨T.terms.map fun a => (-a.1, a.2), -T.remSup, -T.remInf, T.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
