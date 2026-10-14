module

public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Zoo.Real.Zoo

@[expose] public section

/-!
# `ContSet/Zoo/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =======================================  `Zoo.uminus`  ======================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's unary `-` (`aux_s_uminus`): every member negated. -/
def Zoo.uminus (Z : Zoo n) : Zoo n := ⟨Z.taylm.map Taylm.uminus, Z.ivl.map Interval.uminus⟩

end CORALean.Real


-- =======================================  `Zoo.uplus`  ======================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- CORA's unary `+`: the zoo unchanged. -/
def Zoo.uplus (Z : Zoo n) : Zoo n := Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
