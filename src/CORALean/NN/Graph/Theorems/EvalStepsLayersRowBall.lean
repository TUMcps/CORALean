module

public import CORALean.NN.Graph.Theorems.EvalStepsLayersRowMask
public import CORALean.NN.Graph.Theorems.EvalStepsLayersSubmatrix

@[expose] public section

/-!
# `[1, Sec. 4.3]`'s locality for the layered network: a ball's `κ` needs no `hclosed`

`evalStepsLayers_submatrix`'s `hclosed` is what `mask (ball A v L)` satisfies by construction
once `κ`'s image is the ball itself, so the masked chain restricted to `κ` is the chain on the
subgraph and `evalStepsLayers_row_mask` at `S = ball A v L` does the rest. The same argument as
`evalSteps_row_ball`, with a layer per node after each step.

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Row `v` of an `L`-step layered chain equals `k₀`'s row of the chain run on the subgraph `κ`
enumerates the `L`-ball by. -/
theorem GNN.evalStepsLayers_row_ball {N K F : ℕ} (A : Mat ℝ N N) (v : Fin N) (L : ℕ)
    (κ : Fin K → Fin N) (hinj : Function.Injective κ)
    (hκ : ∀ i, (∃ k, κ k = i) ↔ i ∈ GNN.ball A v L)
    (g : Fin L → Vec ℝ F → Vec ℝ F) (X : Mat ℝ N F) (k₀ : Fin K) (hk₀ : κ k₀ = v) : -- --- STMT ---
    GNN.evalStepsLayers (GNN.messagePassing A) L g X v
      = GNN.evalStepsLayers ((GNN.messagePassing A).submatrix κ κ) L g
          (X.submatrix κ id) k₀ := by -- --- PROOF ---
  set S := GNN.ball A v L
  set P := GNN.messagePassing A
  -- masking to exactly the ball changes nothing at `v`
  have hmask : GNN.evalStepsLayers P L g X v = GNN.evalStepsLayers (GNN.mask S P) L g X v :=
    GNN.evalStepsLayers_row_mask A v S L (subset_refl _) g X X (fun u _ => rfl)
  -- `κ`'s image being exactly `S` gives both `hclosed` and the submatrix agreement
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
  have hstep := GNN.evalStepsLayers_submatrix (GNN.mask S P) κ hinj hclosed L g X
  rw [hsub] at hstep
  rw [hmask, ← hk₀]
  exact congrFun hstep k₀

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
