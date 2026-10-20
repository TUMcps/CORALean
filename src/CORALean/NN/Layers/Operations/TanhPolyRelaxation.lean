module

public import CORALean.NN.Layers.Operations.DoubleRounding
public import CORALean.NN.Layers.Operations.PolyRelaxationOfAffineConj
public import CORALean.NN.Layers.Operations.SigmoidPolyRelaxation

@[expose] public section

/-!
# The polynomial relaxation at tanh

`sigmoidPolyRelaxation` read through `tanh t = 2 σ(2t) - 1`: `PolyRelaxation.ofAffineConj` at
`ra = rb = 2`, both doublings by self-addition, and `c = -1`, which `neg one` stores exactly.

## Inputs
* `N` – number of grid intervals
* `k` – reduction depth of the exponential
* `c` – fit coefficients for each box
* `dx` – grid spacing for each box
* `p` – proposed sample grid for each box

## Output
* polynomial relaxation of tanh through the sigmoid's
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   12-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sigmoidPolyRelaxation` read through `tanh_eq_sigmoid`: `a = b = 2`, `c = -1`. -/
def tanhPolyRelaxation {N : ℕ} (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofAffineConj (sigmoidPolyRelaxation k c dx p) doubleRounding doubleRounding
    (neg one)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
