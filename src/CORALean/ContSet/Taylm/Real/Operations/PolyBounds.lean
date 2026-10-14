module

public import CORALean.ContSet.Taylm.Real.Operations.TermBounds

@[expose] public section

/-!
# The range of a term list over the box

The term ranges summed: CORA's `interval` with `opt_method = 'int'`, outer and no tighter.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.polyBounds (L : List (ℝ × (Fin n → ℕ))) : Interval ℝ :=
  ⟨(L.map fun a => (Taylm.termBounds a).inf).sum, (L.map fun a => (Taylm.termBounds a).sup).sum⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
