module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The slice of a box through a point

`jacobiSlice x̃ ind v` is `x̃` with coordinate `ind i` replaced by `vᵢ`: the affine map
`v ↦ x̃ + P (v - x̃ ∘ ind)`, `P` the selection matrix of `ind`. It is the slice
`u₁ ↦ (u₁, ũ₂)` on which an inner-range test of `f : ℝᵐ → ℝⁿ` reduces to a square one: the
test picks the `n` columns `ind` of the Jacobian and holds the other coordinates at the
midpoint.

## Inputs
* `xc` – base point
* `ind` – indices of the replaced coordinates
* `v` – new values

## Output
* the base point with the selected coordinates replaced
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `xc` with coordinate `ind i` replaced by `v i`. -/
def jacobiSlice (xc : Fin m → ℝ) (ind : Fin n → Fin m) (v : Fin n → ℝ) : Fin m → ℝ :=
  xc + (Matrix.of fun k i => if ind i = k then (1 : ℝ) else 0) *ᵥ (v - fun i => xc (ind i))


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
