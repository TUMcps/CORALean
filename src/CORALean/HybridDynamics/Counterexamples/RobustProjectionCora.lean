module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Location.robustProjectionCora`: CORA's `aux_robustProjection`, as printed

CORA's `guardIntersect_zonoGirard`, `aux_robustProjection(D, n, gamma, lb, ub)`: when exactly one
entry of `n_ = Dᵀ n` has `|n_ᵢ| ≥ eps`, the basis is read as orthogonal to the hyperplane
`n x = γ` and the interval in that coordinate is pinned to `val = γ n_ᵢ`. The coordinate of the
unit column `D(:, i)` on the hyperplane is `γ / n_ᵢ`, which is `γ n_ᵢ` only for `n_ᵢ = ±1`.

# `Location.robustProjectionCora` pins the box off the hyperplane

For the guard `2 x₁ = 4` (normal `(2, 0)`, `γ = 4`, hyperplane `x₁ = 2`) and the standard basis,
`aux_robustProjection` pins the first coordinate to `γ · 2 = 8`: whatever the bounds it is given,
the box it returns contains no point of the hyperplane.

## Inputs
* `lb` – lower box bound
* `ub` – upper box bound

## Hypotheses
* none

## Conclusion
* the projected box excludes every guard point
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
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

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- The box of `aux_robustProjection` at `D = 1`, `n = (2, 0)`, `γ = 4` misses the hyperplane. -/
theorem Location.robustProjectionCora_counterexample (lb ub : Vec ℝ 2) : -- --- CONCL ---
    ∀ x : Vec ℝ 2, x ⬝ᵥ ![2, 0] = 4 →
      ¬ ∀ k, (Location.robustProjectionCora (1 : Mat ℝ 2 2) ![2, 0] 4 lb ub).1 k ≤ x k ∧
        x k ≤
          (Location.robustProjectionCora (1 : Mat ℝ 2 2) ![2, 0] 4 lb ub).2 k := by -- --- PROOF ---
  intro x hx hbox
  have h0 : x 0 = 2 := by
    simp [dotProduct, Fin.sum_univ_two] at hx
    linarith
  have hn : ((1 : Mat ℝ 2 2)ᵀ *ᵥ ![2, 0]) = ![2, 0] := by simp
  have h1 : ((2 : ℝ) ^ 52)⁻¹ ≤ 2 :=
    le_trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ 52 := by
    positivity
  -- only the first column is read as parallel to the normal
  have hf : (List.finRange 2).filter
      (fun i => decide ((2 : ℝ) ^ (-52 : ℤ) ≤ |((1 : Mat ℝ 2 2)ᵀ *ᵥ ![2, 0]) i|)) = [0] := by
    rw [hn]
    simp [List.finRange_succ, List.filter]
    split <;> split <;> simp_all <;> linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) 52]
  have := hbox 0
  simp only [Location.robustProjectionCora, hf] at this
  simp [h0] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
