module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Scattering a vector to coordinates

The entries of `v` placed at the coordinates `σ` of a larger vector, zero elsewhere: MATLAB's
`x(σ) = v` on a zero vector. `resolve` of a reset writes a block `B(stateBinds{i}, ...)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def scatter {n N : ℕ} (σ : Fin n → Fin N) (v : Fin n → ℝ) : Fin N → ℝ :=
  fun a => ∑ r, if σ r = a then v r else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
