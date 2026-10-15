module

public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Graph.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `GNN.messagePassingEnclosure_h_le`

The cubic bound [1, Thm. 1] carries into the message-passing steps, with the
node count in the constant.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cubic bound [1, Thm. 1] carries into the message-passing steps, with the
node count in the constant. -/
theorem GNN.messagePassingEnclosure_h_le (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hm : 1 ≤ m) : (GNN.messagePassingEnclosure R A U).h
      ≤ ((N + 2) * (N + 2) + 1) * (N + 2) * m ^ 3 := by -- --- PROOF ---
  rw [GNN.messagePassingEnclosure_h]
  -- at one edge or more, every factor of the padded set fits inside `(N + 2) * m`
  have hb : m + N + 1 ≤ (N + 2) * m := by
    have h : (N + 1) * 1 ≤ (N + 1) * m := Nat.mul_le_mul (le_refl (N + 1)) hm
    linarith
  have hone : 1 ≤ m * m := by
    have h := Nat.mul_le_mul hm hm
    simpa using h
  -- the square first, then the third factor, so each step is one `Nat.mul_le_mul`
  have hsq : (m + N + 1) * (m + N + 1) + 1 ≤ ((N + 2) * (N + 2) + 1) * (m * m) := by
    calc (m + N + 1) * (m + N + 1) + 1
        ≤ ((N + 2) * m) * ((N + 2) * m) + m * m := Nat.add_le_add (Nat.mul_le_mul hb hb) hone
      _ = ((N + 2) * (N + 2) + 1) * (m * m) := by ring
  calc ((m + N + 1) * (m + N + 1) + 1) * (m + N + 1)
      ≤ (((N + 2) * (N + 2) + 1) * (m * m)) * ((N + 2) * m) := Nat.mul_le_mul hsq hb
    _ = ((N + 2) * (N + 2) + 1) * (N + 2) * m ^ 3 := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
