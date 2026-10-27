module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The polyhedral asymmetric norm

`[1, Def. 3]`: for a polytope `{η_i x ≤ h_i}` with every `h_i ≠ 0`,
`S_P(x) = max {0, η₁ x / h₁, …, η_s x / h_s}`. The `0` makes it a fold of `max` from `0`
over the rows.

## Inputs
* `H` – `s × n` matrix
* `h` – vector of length `s`
* `x` – point of length `n`

## Output
* `S_P(x)`, `[1, Def. 3]`

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {s n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S_P(x)`, `[1, Def. 3]`. -/
noncomputable def HPolytope.polyNorm (H : Mat ℝ s n) (h : Vec ℝ s) (x : Vec ℝ n) : ℝ :=
  Finset.univ.fold max 0 fun i => (H *ᵥ x) i / h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
