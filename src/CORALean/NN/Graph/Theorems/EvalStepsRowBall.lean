module

public import CORALean.NN.Graph.Theorems.EvalStepsRowMask
public import CORALean.NN.Graph.Theorems.EvalStepsSubmatrix

@[expose] public section

/-!
# `[1, §4.3]`'s locality, assembled: a ball's `κ` needs no `hclosed` hypothesis

`evalSteps_submatrix`'s `hclosed` is exactly what `mask (ball A v L)` satisfies
by construction, once `κ`'s image is the ball itself (`hκ`): nothing outside
the image feeds a masked entry, and the masked and unmasked matrices agree on
`κ`'s own rows and columns. `evalSteps_row_mask` at `S = ball A v L`, `X = Y`,
does the rest — no second induction, since restricting is now a corollary of
masking rather than a fact proved from scratch.

## Inputs
* `N` – number of nodes
* `K` – number of kept nodes
* `F` – feature width
* `A` – adjacency matrix
* `v` – node of interest
* `L` – number of steps
* `κ` – indices of the kept nodes
* `W` – weights of the steps
* `X` – node-feature matrix
* `k₀` – index of the node of interest among the kept ones

## Hypotheses
* `hinj` – kept indices are distinct
* `hκ` – kept nodes are exactly the ball
* `hk₀` – index names the node of interest

## Conclusion
* the node's row of the full chain equals its row on the subgraph

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step chain equals `k₀`'s row of the same chain run on the
subgraph `κ` enumerates the `L`-ball by. -/
theorem GNN.evalSteps_row_ball {N K F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : ∀ i, (∃ k, κ k = i) ↔ i ∈ GNN.ball A v L)
    (W : Fin L → Mat ℝ F F) (X : Mat ℝ N F) (k₀ : Fin K) (hk₀ : κ k₀ = v) : -- --- CONCL ---
    GNN.evalSteps (GNN.messagePassing A) L W X v
      = GNN.evalSteps ((GNN.messagePassing A).submatrix κ κ) L W
          (X.submatrix κ id) k₀ := by -- --- PROOF ---
  set S := GNN.ball A v L
  set P := GNN.messagePassing A
  -- masking to exactly the ball changes nothing at `v`: `hS` and `hXY` are both trivial
  have hmask : GNN.evalSteps P L W X v = GNN.evalSteps (GNN.mask S P) L W X v :=
    GNN.evalSteps_row_mask A v S L (subset_refl _) W X X (fun u _ => rfl)
  -- `κ`'s image being exactly `S` (`hκ`) gives both `hclosed` and the submatrix agreement
  have hclosed : ∀ k i, (∀ l, κ l ≠ i) → GNN.mask S P (κ k) i = 0 := by
    intro k i hi
    have hiS : i ∉ S := by
      intro h
      obtain ⟨l, hl⟩ := (hκ i).mpr h
      exact hi l hl
    simp [GNN.mask, hiS]
  have hsub : (GNN.mask S P).submatrix κ κ = P.submatrix κ κ := by
    funext k k'
    have hk : κ k ∈ S := (hκ (κ k)).mp ⟨k, rfl⟩
    have hk' : κ k' ∈ S := (hκ (κ k')).mp ⟨k', rfl⟩
    simp [GNN.mask, hk, hk']
  have hstep := GNN.evalSteps_submatrix (GNN.mask S P) κ hinj hclosed L W X
  rw [hsub] at hstep
  rw [hmask, ← hk₀]
  exact congrFun hstep k₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
