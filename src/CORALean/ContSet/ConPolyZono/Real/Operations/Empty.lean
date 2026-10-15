module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.empty`

CORA's `conPolyZono.empty(n)`: no generators and a single constraint row that cannot hold. The
row has the empty constraint matrix (`q = 0`, so `A μ = 0`) and the crossed bound `[1, 0]`,
so `1 ≤ 0` is required of the zero vector and no factor vector is admitted.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono.empty(n)`: the center `0`, no generators, and the unsatisfiable row `1 ≤ 0`. -/
def ConPolyZono.empty (n : ℕ) : ConPolyZono (Vec ℝ n) :=
  ⟨0, 0, 0, 1, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, ⟨fun _ => 1, fun _ => 0⟩, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
