module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.empty`

CORA's `conPolyZono.empty(n)`: no generators and a single constraint row that cannot hold. The
row has the empty constraint matrix (`q = 0`, so `A μ = 0`) and the right-hand side `1`, so
`0 = 1` is required of every factor vector and none is admitted.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono.empty(n)`: the center `0`, no generators, and the unsatisfiable row `0 = 1`. -/
def ConPolyZono.empty (n : ℕ) : ConPolyZono (Vec ℝ n) :=
  ⟨0, 0, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨1, 0, 0, Fin.elim0, fun _ => 1, fun _ => .eq⟩,
    fun _ => rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
