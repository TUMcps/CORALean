import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `Zonotope.boundaryPoint`

CORA's `@zonotope/boundaryPoint.m`: where the ray from `startPoint` (default the centre) in
direction `dir` leaves the zonotope. For `n > 1` CORA solves the linear program
`min -t` over `t ≥ 0`, `β ∈ [-1, 1]ᵐ` with `t·dir - Gβ = c - startPoint`, and returns
`startPoint - fval·dir`, i.e. `startPoint + t*·dir` with `t*` the largest `t` such that
`startPoint + t·dir` is in the zonotope. The two shortcuts (`n = 1`: `c ± Σ|gⱼ|`; the start at the
centre: `c + dir / ‖dir‖_Z`) are the same point. Here `t*` is the supremum, which the LP
attains; the definition is not computable (the solver is replaced by the specification).
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/boundaryPoint(Z, dir, startPoint)`. -/
noncomputable def Zonotope.boundaryPoint (Z : Zonotope α) (dir start : α) : α :=
  -- the largest step along `dir` that stays in `Z` (CORA's LP optimum `-fval`)
  let t := sSup {t : ℝ | 0 ≤ t ∧ start + t • dir ∈ Z.construct}
  start + t • dir

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
