module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack
public import CORALean.NN.Graph.Definitions.ActLayer
public import CORALean.NN.Graph.Operations.GcnShared

@[expose] public section

/-!
# The graph part of `Alg. 1`, on matrix polynomial zonotopes

[1, Alg. 1], lines 3 to 6: `L` message-passing steps, each a graph convolution `P ⊡ H W`
([1, Prop. 5]) and then the enclosure of its activation ([1, Prop. 1]), at one uncertain graph
`P`. The enclosure's new independent generators are made dependent before the next convolution,
which `bilin` needs to see them, and `P` is padded by the factors that adds, so an edge is the same
factor at every step. `P` is [1, Prop. 4]'s enclosure padded against the input set.

## Inputs
* none

## Output
* polynomial zonotope after the convolution and activation steps

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L` steps `H ↦ dependent (act (P ⊡ H W))`, `P` padded by what each step adds. -/
def GNN.gcnActSteps :
    ∀ (L : ℕ) (c : ℕ → ℕ) (_ : ∀ s, Mat ℝ (c s) (c (s + 1)))
      (_ : ∀ s, GNN.ActLayer N (c (s + 1))) (P : PolyZonotope (Mat ℝ N N))
      (H : PolyZonotope (Mat ℝ N (c 0))), P.p = H.p → PolyZonotope (Mat ℝ N (c L))
  | 0, _, _, _, _, H, _ => H
  | L + 1, c, W, acts, P, H, hp =>
    let H₁ := GNN.gcnShared (W 0) P H hp                      -- P ⊡ H W
    let H₂ := (acts 0).act H₁                                  -- enclose the activation
    GNN.gcnActSteps L (fun s => c (s + 1)) (fun s => W (s + 1)) (fun s => acts (s + 1))
      (P.padBack H₂.q) H₂.dependent
      (by show P.p + H₂.q = H₂.p + H₂.q; rw [(acts 0).p_eq]; rfl)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
