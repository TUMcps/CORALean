module

public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Taylm.Real.Operations.Minus
public import CORALean.ContSet.Taylm.Real.Taylm
public import Mathlib.Data.Matrix.Mul
public import CORALean.ContSet.Taylm.Real.Operations.QuadTerms

@[expose] public section

/-!
# The quadratic fast bounder

[1, Sec. 3]: `l(P + I) = l(P - Q_{x₀}) + l(Q_{x₀}) + l(I)` with `l(Q_{x₀}) = 0` for a positive
semidefinite `H`; `l(P - Q_{x₀}) + l(I)` is the lower bound of the model `T - Q_{x₀}`.

## Inputs
* `T` – Taylor model
* `H` – Hessian matrix
* `x0` – expansion point

## Output
* lower bound of the model by the quadratic fast bounder

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

noncomputable def Taylm.aux_quadForm (H : Mat ℝ n n) (x0 : Vec ℝ n) (N : ℕ) : Taylm n :=
  ⟨Taylm.quadTerms H x0, ⟨0, 0⟩, N⟩


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.qfbLower (T : Taylm n) (H : Mat ℝ n n) (x0 : Vec ℝ n) : ℝ :=
  (T.minus (Taylm.aux_quadForm H x0 T.maxOrder)).bounds.inf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
