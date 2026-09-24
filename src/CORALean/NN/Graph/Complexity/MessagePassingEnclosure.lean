import CORALean.NN.Graph.MessagePassingEnclosure

/-!
# `GNN.messagePassingEnclosure`'s counts

[1, Prop. 4]'s `O(h³)` as the count itself: two `bilin`s over the `m + N` shared
factors — one per uncertain edge and one residual per node — leave `𝒫` with
`((m+N+1)² + 1)(m+N+1)` dependent generators and no independent ones. `rfl`
against the structure instances in `MessagePassingEnclosure.lean` and
`Operations/Bilin.lean`.

Cubic in `m + N` where [1] is cubic in the edge count alone: `sqrtBroadcast`
spends a residual factor on *every* node, where [1] bounds the nodes with an
uncertain degree by `2h`. `messagePassingEnclosure_h_le` is the form
[1, Thm. 1] composes — the node count sits in the constant, so the growth in
the uncertain edges is what the bound reads.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
