module

public import CORALean.NN.Graph.Complexity.Space.Theorems.GcnActStepsHLe
public import CORALean.NN.Graph.Complexity.Space.Theorems.MessagePassingEnclosureHLe
public import CORALean.NN.Graph.Operations.Alg1Node
public import CORALean.NN.Graph.Complexity.Space.Theorems.Alg1NodeEqGcnActSteps

@[expose] public section

/-!
# `GNN.alg1Node_h_le`

[1, Thm. 1 (generators)]: `Alg. 1` on the graph layers leaves at most `K^L m^(3L) (h_x + 1 + L
ν)` generators, `h_x` the input's dependent and independent ones.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1 (generators)]: `Alg. 1` on the graph layers leaves at most `K^L m^(3L) (h_x + 1 + L
ν)` generators, `h_x` the input's dependent and independent ones. -/
theorem GNN.alg1Node_h_le (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (hm : 1 ≤ m) (L : ℕ) (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
    (acts : ∀ s, GNN.ActLayer N (c (s + 1))) (ν : ℕ) (hadd : ∀ s, s < L → (acts s).AddsAtMost ν)
    (X : PolyZonotope (Mat ℝ N (c 0))) :
    (GNN.alg1Node R A U L c W acts X).h + 1
      ≤ (((N + 2) * (N + 2) + 1) * (N + 2) + 2) ^ L * m ^ (3 * L)
        * (X.h + X.q + 1 + L * ν) := by -- --- PROOF ---
  rw [GNN.alg1Node_eq_gcnActSteps]
  refine (GNN.gcnActSteps_h_le ν L c W acts hadd _ _ rfl).trans ?_
  -- the base of the power: the enclosure's cubic with the `+2` of a step folded in
  have hmpe : (GNN.messagePassingEnclosure R A U).h + 2
      ≤ (((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3 := by
    have h := GNN.messagePassingEnclosure_h_le R A U hm
    have hc : 1 ≤ m ^ 3 := Nat.one_le_pow 3 m (by omega)
    calc (GNN.messagePassingEnclosure R A U).h + 2
        ≤ ((N + 2) * (N + 2) + 1) * (N + 2) * m ^ 3 + 2 * m ^ 3 := by linarith
      _ = (((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3 := by ring
  show ((GNN.messagePassingEnclosure R A U).h + 2) ^ L * (X.h + X.q + 1 + L * ν) ≤ _
  calc ((GNN.messagePassingEnclosure R A U).h + 2) ^ L * (X.h + X.q + 1 + L * ν)
      ≤ ((((N + 2) * (N + 2) + 1) * (N + 2) + 2) * m ^ 3) ^ L * (X.h + X.q + 1 + L * ν) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hmpe L) (le_refl _)
    _ = _ := by rw [mul_pow, ← pow_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
