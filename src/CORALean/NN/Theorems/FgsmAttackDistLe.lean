module

public import CORALean.NN.Operations.FgsmAttack

@[expose] public section

/-!
# The FGSM attack stays within `ε` of its input

Each coordinate moves by `ε * sign(·)`, and a sign has absolute value at most one, so
`‖z - x‖∞ ≤ ε` for `ε ≥ 0`, the guarantee CORA documents.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Chain.fgsmAttack_dist_le (c : Chain n m) (x : Vec ℝ n) (t : Vec ℝ m) {ε : ℝ}
    (hε : 0 ≤ ε) (lossDer : Vec ℝ m → Vec ℝ m → Vec ℝ m) (i : Fin n) :
    |c.fgsmAttack x t ε lossDer i - x i| ≤ ε := by
  show |x i + ε * Real.sign _ - x i| ≤ ε
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hε]
  rcases Real.sign_apply_eq (c.backprop x (lossDer t (c.eval x)) i) with h | h | h <;>
    rw [h] <;> simp [hε]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
