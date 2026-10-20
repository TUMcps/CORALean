module

public import CORALean.ContSet.Interval.Float.Operations.MatMul
public import CORALean.ContSet.Interval.Float.Operations.Submatrix

@[expose] public section

/-!
# Message passing on a shrinking node set, at float
`GNN.reducedSteps` on interval matrices: `L` steps of `Y ↦ P[κ (k+1), κ k] Y W k`, with `P` the
stored `D̃^(-1/2) Ã D̃^(-1/2)` as an interval matrix and every product `Interval.matMul`, rounded
outward. The kept node sets are enumerated by `κ k : Fin (c k) → Fin N`, the rows of the features
before step `k`, so the matrices are the ordinary `Mat 𝕋`. The features start on `κ 0` [1, §4.3].

## Inputs
* `P` – interval message-passing matrix

## Output
* interval features on the last kept node set after the steps

## References

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {N F : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GNN.reducedStepsFloat (P : Interval (Mat 𝕋 N N)) :
    (L : ℕ) → (c : ℕ → ℕ) → (κ : (k : ℕ) → Fin (c k) → Fin N) → (W : ℕ → Interval (Mat 𝕋 F F)) →
      Interval (Mat 𝕋 (c 0) F) → Interval (Mat 𝕋 (c L) F)
  | 0, _, _, _, Y => Y
  | L + 1, c, κ, W, Y =>
    GNN.reducedStepsFloat P L (fun k => c (k + 1)) (fun k => κ (k + 1)) (fun k => W (k + 1))
      (Interval.matMul (Interval.matMul (P.submatrix (κ 1) (κ 0)) Y) (W 0))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
