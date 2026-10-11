import CORALean.NN.Graph.Operations.Alg1Node
import CORALean.NN.Graph.Operations.SumPool
import CORALean.NN.Graph.Operations.TailEnclose

/-!
# `Alg. 1` for a graph-level output

[1, Alg. 1], lines 1 to 6 and 9 to 15 (`κ ≠ 2κ'`, the branch the paper labels "node-level"): after
the `κ'` convolution and activation pairs, the global pooling ([1, Prop. 3], here the sum) and the
standard layers after it, a linear layer exactly and an activation by [1, Prop. 1]. The widths
`c (L + t)` of the standard layers continue those of the graph layers, `c L` being the pooled
vector's.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


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
  let H := GNN.alg1Node R A U L c W acts X                           -- 1-6: graph layers
  let H' := GNN.sumPool H                                            -- 10: global pooling (Prop. 3)
  GNN.tailEnclose T (fun t => c (L + t)) f H'                        -- 11-14: standard layers

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
