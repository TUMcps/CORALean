import CORALean.ContSet.Taylm.Real.Operations.TermBounds

/-!
# The range of a term list over the box

The term ranges summed: CORA's `interval` with `opt_method = 'int'`, outer and no tighter.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.polyBounds (L : List (ℝ × (Fin n → ℕ))) : ℝ × ℝ :=
  ((L.map fun a => (Taylm.termBounds a).1).sum, (L.map fun a => (Taylm.termBounds a).2).sum)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
