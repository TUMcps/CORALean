module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront
public import CORALean.NN.Graph.Operations.GcnActSteps
public import CORALean.NN.Graph.Operations.MessagePassingEnclosure

@[expose] public section

/-!
# `Alg. 1` for a node-level output

[1, Alg. 1], lines 1 to 6 and 8 (`κ = 2κ'`, the branch the paper labels "graph-level" and
the paper's text before the algorithm calls node-level): the input set `H₀ ← X`, the
message passing `P` of the uncertain graph ([1, Prop. 4]), and `κ'` pairs of a convolution
([1, Prop. 5]) and the enclosure of an activation ([1, Prop. 1]); the last output is returned.
The input's independent generators are made dependent, which the convolution needs to see them,
and `P` is padded against the input set so an edge is the same factor throughout.

## Inputs
* `R` – relaxation of the activations
* `A` – adjacency matrix
* `U` – uncertain edges
* `L` – number of graph layers
* `c` – layer widths
* `W` – graph layer weights
* `acts` – activation layers
* `X` – input polynomial zonotope

## Output
* polynomial zonotope enclosing the node-level output

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.
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

/-- [1, Alg. 1] for a node-level output: `L` convolution and activation pairs on `X`. -/
noncomputable def GNN.alg1Node (R : Relaxation ℝ) (A : Mat ℝ N N) (U : Fin m → Fin N × Fin N)
    (L : ℕ) (c : ℕ → ℕ) (W : ∀ s, Mat ℝ (c s) (c (s + 1))) (acts : ∀ s, GNN.ActLayer N (c (s + 1)))
    (X : PolyZonotope (Mat ℝ N (c 0))) : PolyZonotope (Mat ℝ N (c L)) :=
  -- 1. `H₀ ← X`, its generators made dependent
  let H₀ := X.dependent
  -- 2. `P ← compute message passing based on G` (Prop. 4)
  let P := GNN.messagePassingEnclosure R A U
  -- 3. `for k′ = 2, …, 2κ′`: `enclose(L^GC, H, P)` (Prop. 5), `enclose(L^ACT, H)` (Prop. 1)
  GNN.gcnActSteps L c W acts (P.padBack H₀.p) (H₀.padFront P.p) rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
