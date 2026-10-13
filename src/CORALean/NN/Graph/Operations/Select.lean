import CORALean.ContSet.ContSet.ContSet

/-!
# The subgraph projection, `[1, Cor. 1]`'s `M`

`select κ` is `I_{|𝒩|}(𝒦,·)`: the identity's rows named by the subgraph's node
indices `κ : Fin K → Fin N`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N K : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[1, Cor. 1]`'s `M = I_{|𝒩|}(𝒦,·)`: the rows of the identity the subgraph names. -/
def GNN.select (κ : Fin K → Fin N) : Mat ℝ K N := (1 : Mat ℝ N N).submatrix κ id

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
