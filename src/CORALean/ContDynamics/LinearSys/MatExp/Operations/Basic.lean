module

public import Mathlib.Analysis.Matrix.Normed
public import CORALean.Global.Tensor

@[expose] public section

/-!
# `ContDynamics/LinearSys/MatExp/Operations`: small declarations

The diagonal similarity `S⁻¹ M S` that a balanced norm reads a matrix through.

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ====================================  `MatExp.scaleConj`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `S⁻¹ M S` for `S = diag s`: the entry `(j, k)` is `M_jk s_k / s_j`. -/
noncomputable def MatExp.scaleConj (s : Fin n → ℝ) (M : Mat ℝ n n) : Mat ℝ n n :=
  diagonal (fun i => (s i)⁻¹) * M * diagonal s

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
