import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# `Zonotope.reduceScottStep`

[1, Sec. 4.3 (new reduction)]: one step of the generator reduction "after Chisci et al. (1996)" that
lift-then-reduce (Sec. 4.3) uses. The state is `(T, R)`, the zonotope `{[T TR], c}`
(`Zonotope.ofEchelon`). A column `r = T⁻¹v` of `R` is chosen. The order-`(n+1)/n` part
`X = {[T v], c}` is replaced by the parallelotope `X̃ = {[T(I + diag|r|)], c}`, Chisci et al.'s
smallest enclosing one for `‖r‖∞ ≤ 1`. The state is then updated by (A.10):
`T := T(I + diag|r|)`, `R := (I + diag|r|)⁻¹R₋`, `R₋` being `R` without `r`. One generator
goes.

Which column is chosen is the caller's: [1] picks the `r` with the least volume error
`v(X̃) − v(X)`, and every choice gives an enclosure (`ofEchelon_reduceScottStep_outer`).
`I + diag|r|` is the diagonal matrix with entries `1 + |r_i|`, and its inverse the one with
entries `(1 + |r_i|)⁻¹`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 4.3 (new reduction)]: column `ind` of `R` removed, (A.10)'s update of `(T, R)`. -/
noncomputable def Zonotope.reduceScottStep {n k : ℕ} (T : Mat ℝ n n) (R : Fin (k + 1) → Vec ℝ n)
    (ind : Fin (k + 1)) : Mat ℝ n n × (Fin k → Vec ℝ n) :=
  let r := R ind                                                    -- r = T⁻¹v
  let D : Mat ℝ n n := diagonal fun i => 1 + |r i|                  -- I + diag|r|
  let Dinv : Mat ℝ n n := diagonal fun i => (1 + |r i|)⁻¹           -- (I + diag|r|)⁻¹
  let T' := T * D                                                   -- T := T(I + diag|r|)
  let R' := fun l => Dinv *ᵥ R (ind.succAbove l)                     -- R := (I + diag|r|)⁻¹R₋
  (T', R')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
