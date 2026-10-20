module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.DependentExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExistsPointOfQZero
public import CORALean.NN.Graph.Operations.Alg1Node
public import CORALean.NN.Graph.Theorems.EvalLayersMemGcnActStepsUncertain

@[expose] public section

/-!
# `Alg. 1` for a node-level output satisfies the problem statement

[1, Thm. 1], soundness: whatever subset of the uncertain edges is present (here any weighting in
`[0, 1]` of them, which contains the subsets) and whatever input of the set `X`, the network
`Φ(X, G)` computed exactly lies in the set `Alg. 1` returns. The input's independent generators are
the first factors (`dependent_exact`); the rest is `evalLayers_mem_gcnActSteps_uncertain`. The
activation enclosures are hypotheses (`ActLayer.Sound`), the content of [1, Prop. 1], which
[1] does not prove.

## Inputs
* `R` – relaxation of the inverse square root
* `A` – adjacency matrix
* `U` – uncertain edges
* `lam` – weights of the uncertain edges
* `L` – number of graph layers
* `c` – layer widths
* `σ` – activation functions
* `W` – graph layer weights
* `acts` – activation layers
* `X` – input polynomial zonotope
* `x` – input point

## Hypotheses
* `hR` – relaxation is sound for the inverse square root
* `hA` – adjacency entries are nonnegative
* `hlam` – edge weights lie in the unit interval
* `hσ` – each activation layer is sound for its function
* `hx` – input point lies in the input set

## Conclusion
* the exact node-level output lies in the enclosure

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

/-- [1, Thm. 1]: the exact output of the node-level network is in `Alg. 1`'s enclosure. -/
theorem GNN.alg1Node_sound (R : Relaxation ℝ) (hR : R.Sound invSqrt) (A : Mat ℝ N N)
    (U : Fin m → Fin N × Fin N) (hA : ∀ i j, 0 ≤ A i j) (lam : Fin m → ℝ)
    (hlam : ∀ e, 0 ≤ lam e ∧ lam e ≤ 1) (L : ℕ) (c : ℕ → ℕ) (σ : ℕ → ℝ → ℝ)
    (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (hσ : ∀ s, (acts s).Sound (σ s)) (X : PolyZonotope (Mat ℝ N (c 0))) {x : Mat ℝ N (c 0)}
    (hx : x ∈ X.construct) : -- --- CONCL ---
    GNN.evalLayers (GNN.messagePassing (GNN.adjAt A U lam)) L c σ W x
      ∈ (GNN.alg1Node R A U L c W acts X).construct := by -- --- PROOF ---
  -- the input is a point of its dependent form, whose independent block is empty
  have hx' : x ∈ X.dependent.construct := X.dependent_exact ▸ hx
  obtain ⟨aH, haH, rfl⟩ := PolyZonotope.exists_point_of_q_zero X.dependent rfl hx'
  exact GNN.evalLayers_mem_gcnActSteps_uncertain R hR A U hA lam hlam L c σ W acts hσ
    X.dependent aH haH

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
