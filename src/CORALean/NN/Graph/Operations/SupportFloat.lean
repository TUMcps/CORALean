import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Tensor

/-!
# The support of a float adjacency matrix
`GNN.support A i j` is `true` unless the stored `A i j` is certified zero: `le` answers `true` only
when it is sure, so both `A i j ≤ 0` and `0 ≤ A i j` certify zero, and a nonzero entry is never
dropped. It is the edge test the float node sets of `reduceGNNForNode` [1, §4.3] run on, the
computable stand-in for `A i j ≠ 0`.

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.support (A : Mat 𝕋 N N) (i j : Fin N) : Bool :=
  !(le (A i j) zero && le zero (A i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
