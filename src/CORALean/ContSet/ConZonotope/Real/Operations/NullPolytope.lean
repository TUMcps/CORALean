module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin

@[expose] public section

/-!
# `ConZonotope.nullPolytope`

The polytope of the full-dimensional branch of CORA's `@conZonotope/center`, in null-space
coordinates: `y ↦ x0 + N y` in the unit box, `[N; -N] y ≤ [1 - x0; 1 + x0]`
(`A_ = A * Neq`, `b_ = b - A * x0` with the box rows `[I; -I]`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `y ↦ x0 + N y` in `[-1, 1]^h`, as `2h` halfspaces over `y`. -/
def ConZonotope.nullPolytope {k : ℕ} (N : Mat ℝ h k) (x0 : Vec ℝ h) : HPolytope (Vec ℝ k) where
  m := h + h
  A := Fin.append (fun i => HPolytope.rowLin N i) (fun i => -HPolytope.rowLin N i)
  b := Fin.append (fun i => 1 - x0 i) (fun i => 1 + x0 i)
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
