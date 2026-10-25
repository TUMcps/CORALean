module

public import CORALean.NN.Graph.Operations.Alg1Graph
public import CORALean.NN.Graph.Operations.OnesRow
public import CORALean.NN.Graph.Theorems.Alg1NodeSound
public import CORALean.NN.Graph.Theorems.PoolingExact
public import CORALean.NN.Graph.Theorems.TailEncloseMem

@[expose] public section

/-!
# `Alg. 1` for a graph-level output satisfies the problem statement

[1, Thm. 1], soundness: the exact graph-level network, the layered convolutions, the sum
over the nodes (`1 H`) and the standard layers `g` after it, lies in `Alg. 1`'s
enclosure. The pooling is exact (`sumPool_exact`) and the standard layers are enclosed layer by
layer (`tailEval_mem_tailEnclose`), each enclosure `f t` containing the image of `g t`
([1, Prop. 1] for an activation, exactness for a linear layer).

## Inputs
* `R` – relaxation of the inverse square root
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `L` – number of graph layers
* `T` – number of layers after the pooling
* `c` – layer widths
* `σ` – activation functions
* `W` – graph layer weights
* `acts` – activation layers
* `g` – exact later layers
* `f` – enclosure maps of the later layers
* `X` – input polynomial zonotope
* `x` – input point

## Hypotheses
* `hR` – relaxation is sound for the inverse square root
* `hA` – adjacency entries are nonnegative
* `hlam` – edge weights lie in the unit interval
* `hσ` – each activation layer is sound for its function
* `hf` – each enclosure map contains its exact layer
* `hx` – input point lies in the input set

## Conclusion
* the exact graph-level output lies in the enclosure

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: the exact graph-level output is in `Alg. 1`'s enclosure. -/
theorem GNN.alg1Graph_sound (R : Relaxation ℝ) (hR : R.IsSound invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (L T : ℕ) (c : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (hσ : ∀ s, (acts s).IsSound (σ s))
    (g : ∀ t, Vec ℝ (c (L + t)) → Vec ℝ (c (L + (t + 1))))
    (f : ∀ t, PolyZonotope (Vec ℝ (c (L + t))) → PolyZonotope (Vec ℝ (c (L + (t + 1)))))
    (hf : ∀ t S x, x ∈ S.construct → g t x ∈ (f t S).construct)
    (X : PolyZonotope (Mat ℝ N (c 0))) {x : Mat ℝ N (c 0)} (hx : x ∈ X.construct) : -- --- CONCL ---
    GNN.tailEval T (fun t => c (L + t)) g
        (fun j => (GNN.onesRow N *
          GNN.evalLayers (GNN.messagePassing (GNN.adjAt A U lam)) L c σ W x) 0 j)
      ∈ (GNN.alg1Graph R A U L T c W acts f X).construct := by -- --- PROOF ---
  -- the pooled graph layers are a point of the pooled enclosure
  have hnode := GNN.alg1Node_sound R hR A U hA lam hlam L c σ W acts hσ X hx
  have hpool : (fun j => (GNN.onesRow N *
      GNN.evalLayers (GNN.messagePassing (GNN.adjAt A U lam)) L c σ W x) 0 j)
      ∈ (GNN.sumPool (GNN.alg1Node R A U L c W acts X)).construct := by
    rw [← GNN.sumPool_exact]
    exact ⟨_, hnode, rfl⟩
  exact GNN.tailEval_mem_tailEnclose T (fun t => c (L + t)) g f hf _ _ hpool

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
