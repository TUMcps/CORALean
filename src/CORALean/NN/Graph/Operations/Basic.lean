module

public import CORALean.Global.Scalar

@[expose] public section

/-!
# `NN/Graph/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {N F₁ F₂ : ℕ}


-- =====================================  `GNN.linearBias`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The bias `b` repeated for each of the `N` nodes.

`output + obj.b'`: the bias row is added to every node's feature row. -/
def GNN.linearBias (N : ℕ) (b : Vec ℝ F₂) : Mat ℝ N F₂ :=
  Matrix.of fun _ f => b f

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
