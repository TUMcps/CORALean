module

public import CORALean.ContSet.Zoo.Real.Zoo
public import CORALean.ContSet.Taylm.Real.Operations.Uminus
public import CORALean.ContSet.Interval.Real.Operations.Uminus

@[expose] public section

/-!
# `Zoo.uminus`

CORA's unary `-` (`aux_s_uminus`): every member negated.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.uminus (Z : Zoo n) : Zoo n := ⟨Z.taylm.map Taylm.uminus, Z.ivl.map Interval.uminus⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
