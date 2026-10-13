import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul

/-!
# `Location.robustProjectionCora`: CORA's `aux_robustProjection`, as printed

CORA's `guardIntersect_zonoGirard`, `aux_robustProjection(D, n, gamma, lb, ub)`: when exactly one
entry of `n_ = Dᵀ n` has `|n_ᵢ| ≥ eps`, the basis is read as orthogonal to the hyperplane
`n x = γ` and the interval in that coordinate is pinned to `val = γ n_ᵢ`. The coordinate of the
unit column `D(:, i)` on the hyperplane is `γ / n_ᵢ`, which is `γ n_ᵢ` only for `n_ᵢ = ±1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_robustProjection`, one named `let` per line of the MATLAB. -/
noncomputable def Location.robustProjectionCora (D : Mat ℝ n n) (nv : Vec ℝ n) (γ : ℝ)
    (lb ub : Vec ℝ n) : Vec ℝ n × Vec ℝ n :=
  -- `n_ = D' * n`
  let n_ : Vec ℝ n := Dᵀ *ᵥ nv
  -- `ind = find(abs(n_) >= eps)`, with `eps = 2^-52`
  let ind : List (Fin n) := (List.finRange n).filter fun i => decide ((2 : ℝ) ^ (-52 : ℤ) ≤ |n_ i|)
  -- `if length(ind) == 1`
  match ind with
  | [i] =>
    -- `val = gamma * n_(ind)`
    let val : ℝ := γ * n_ i
    -- `lb(ind) = val; ub(ind) = val`
    (Function.update lb i val, Function.update ub i val)
  | _ => (lb, ub)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
