module

public import CORALean.NN.Graph.Operations.MessagePassingEnclosure
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `GNN.messagePassingEnclosure`'s counts

[1, Prop. 4]'s `O(h³)` as the count itself: two `bilin`s over the `m + N` shared
factors leave `𝒫` with `((m+N+1)² + 1)(m+N+1)` dependent generators and no
independent ones, `rfl` against the structure instances. Cubic in `m + N` where
[1] is cubic in the edge count alone: `sqrtBroadcast` spends a residual factor on
*every* node. `messagePassingEnclosure_h_le` is the form [1, Thm. 1] composes, the
node count in the constant.

`messagePassingEnclosure_h_isBigO` is [1, Prop. 4] in `O` notation: `O(m³)` in
the uncertain edges, along a family of edge sets growing with `m`, the node count
and the relaxation held fixed. `messagePassingEnclosure_h_le` is its constant.

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

theorem GNN.messagePassingEnclosure_p (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : (GNN.messagePassingEnclosure R A U).p = m + N := rfl

theorem GNN.messagePassingEnclosure_h (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : (GNN.messagePassingEnclosure R A U).h
      = ((m + N + 1) * (m + N + 1) + 1) * (m + N + 1) := rfl

theorem GNN.messagePassingEnclosure_q (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) : (GNN.messagePassingEnclosure R A U).q = 0 := rfl

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


/-- The enclosure of [1, Prop. 4] grows cubically in the number of uncertain
edges, at a fixed graph size. -/
theorem GNN.messagePassingEnclosure_h_isBigO (R : Relaxation ℝ) (A : Mat ℝ N N)
    (U : ∀ m : ℕ, Fin m → Fin N × Fin N) :
    (fun m : ℕ => (((GNN.messagePassingEnclosure R A (U m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => (m : ℝ) ^ 3 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound ((((N + 2) * (N + 2) + 1) * (N + 2) : ℕ) : ℝ)
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  -- the bound is a statement about naturals, so the cast is the last step
  have h := GNN.messagePassingEnclosure_h_le R A (U m) hm
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
