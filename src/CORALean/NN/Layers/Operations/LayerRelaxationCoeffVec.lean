module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# A layer's fits, one coefficient vector per degree

Neuron `i`'s coefficient of `t ^ k`, from its own fit on its own range: one vector per degree,
which is how a polynomial zonotope's `evalPoly` reads a coefficient, so one call carries `n`
different polynomials.

## Inputs
* `P` – relaxation of every neuron
* `I` – box of the layer's input
* `k` – monomial degree

## Output
* every neuron's coefficient of that degree
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `i`'s coefficient of `t ^ k`, from its own fit on its own range. -/
def LayerRelaxation.coeffVec (P : LayerRelaxation 𝕋 n m) (I : Interval (Vec 𝕋 n))
    (k : Fin (m + 1)) : Vec 𝕋 n := fun i => (P i).coeffs (I.inf i) (I.sup i) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
