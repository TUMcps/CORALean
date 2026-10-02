import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.empty`

CORA's `conPolyZono.empty(n)`: no generators and a single constraint row that cannot hold. The
row has the empty constraint matrix (`s = 0`, so `A μ = 0`) and the crossed bound `[1, 0]`,
so `1 ≤ 0` is required of the zero vector and no factor vector is admitted.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `conPolyZono.empty(n)`: the centre `0`, no generators, and the unsatisfiable row `1 ≤ 0`. -/
def ConPolyZono.empty (n : ℕ) : ConPolyZono (Vec ℝ n) :=
  ⟨0, 0, 0, 1, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, ⟨fun _ => 1, fun _ => 0⟩, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
