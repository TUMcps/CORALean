import Mathlib.Data.Sign.Basic
import Mathlib.Data.Matrix.Mul
import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.underapproximate`

CORA's `@zonotope/underapproximate(Z, S)`: for every direction `S_i` (a column of `S`) the two
vertices `c ± Σ_j sign(S_iᵀ g_j) g_j`, returned as the `2k` columns of a matrix. Here the pair for
direction `i` is `underapproximate Z S i true` and `underapproximate Z S i false` (CORA's columns
`2i-1` and `2i`).
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/underapproximate`: `c + Σ_j sign(S_iᵀ g_j) g_j` for `true`, `c - Σ_j ..` for
`false`, at each direction `S i`. -/
noncomputable def Zonotope.underapproximate {n k : ℕ} (Z : Zonotope (Vec ℝ n))
    (S : Fin k → Vec ℝ n) : Fin k → Bool → Vec ℝ n := fun i b =>
  Z.c + (if b then (1 : ℝ) else -1) •
    ∑ j, ((SignType.sign (S i ⬝ᵥ Z.G j) : SignType) : ℝ) • Z.G j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
