module

public import CORALean.NN.Graph.Operations.Alg1Node
public import CORALean.NN.Graph.Operations.SumPool
public import CORALean.NN.Graph.Operations.TailEnclose

@[expose] public section

/-!
# `Alg. 1` for a graph-level output

[1, Alg. 1], lines 1 to 6 and 9 to 15 (`κ ≠ 2κ'`, the branch the paper labels "node-level"): after
the `κ'` convolution and activation pairs, the global pooling ([1, Prop. 3], here the sum) and the
standard layers after it, a linear layer exactly and an activation by [1, Prop. 1]. The widths
`c (L + t)` of the standard layers continue those of the graph layers, `c L` being the pooled
vector's.

## Inputs
* `R` – relaxation of the activations
* `A` – adjacency matrix
* `U` – uncertain edges
* `L` – number of graph layers
* `T` – number of layers after the pooling
* `c` – layer widths
* `W` – graph layer weights
* `acts` – activation layers
* `f` – enclosure maps of the later layers
* `X` – input polynomial zonotope

## Output
* polynomial zonotope enclosing the graph-level output

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] for a graph-level output: `Alg. 1` on the graph layers, then pooling and `T`
standard layers enclosed by `f`. -/
noncomputable def GNN.alg1Graph (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (L T : ℕ) (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1)))
    (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (f : ∀ t, PolyZonotope (Vec ℝ (c (L + t))) → PolyZonotope (Vec ℝ (c (L + (t + 1)))))
    (X : PolyZonotope (Mat ℝ N (c 0))) : PolyZonotope (Vec ℝ (c (L + T))) :=
  -- 1. `H₀ ← X`, `P` and the `κ′` graph layer pairs of lines 1-6, up to `H_{2κ′}`
  let H := GNN.alg1Node R A U L c W acts X
  -- 10. `H_{2κ′+1} ← L^GP(H_{2κ′}, G)`, the global pooling layer (Prop. 3)
  let H_pool := GNN.sumPool H
  -- 11. `for k = 2κ′+2, …, κ`: `H_k ← L^LIN(H_{k-1})`, `H_{k+1} ← enclose(L^ACT, H_k)` (Prop. 1)
  let H_κ := GNN.tailEnclose T (fun t => c (L + t)) f H_pool
  -- 15. `Y ← H_κ`
  H_κ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
