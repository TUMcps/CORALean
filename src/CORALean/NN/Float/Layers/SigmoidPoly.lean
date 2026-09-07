import CORALean.NN.Float.Layers.PolyDerivBound
import CORALean.NN.Float.Layers.PolyOfSampling
import CORALean.NN.Float.Layers.Sigmoid

/-!
# The polynomial relaxation at the sigmoid, over a floating-point scalar

The first float activation at which `PolyRelaxation.ofSampling` can be
instantiated, and the first `Float.PolyRelaxation` anything can build:
`sigmoidEnclosure` is `σ` at a float, `sigmoidDerivLo`/`sigmoidDerivHi` bracket
`σ'` over the box, and `polyDerivBoundUp` turns that bracket into the `M` the
sampling bound asks for. Nothing beyond assembly is left.

`noncomputable`, for the reason `Layer.sigmoid` already is: `Real.sigmoid`
indexes the type and so reaches the constructor as an argument. Every field
stored is a float expression, so what that costs is `#eval`, not arithmetic.

The fit and the grid stay parameters, and neither owes a proof: any array of
floats is a fit, and a grid that fails `gridChecked` costs precision rather than
soundness. The scalar has no linear solve, so there is no default fit for this
file to prefer, and CORA's least squares would arrive here unverified anyway.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n N : ℕ}

/-- `ofSampling` at the sigmoid: `M` is `Sigmoid`'s derivative bracket against
the fit's own, the fit `c` and the grid `p`, `dx` free. -/
noncomputable def sigmoidPolyRelaxation (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 Real.sigmoid m :=
  PolyRelaxation.ofSampling (sigmoidEnclosure k) c
    (fun l u => polyDerivBoundUp (c l u) (sigmoidDerivLo (sigmoidEnclosure k) l u)
      (sigmoidDerivHi (sigmoidEnclosure k) l u) l u) dx p Real.hasDerivAt_sigmoid
    fun l u x hx hx' => abs_sub_evalPolyDeriv_le
      (sigmoidDerivLo_le (sigmoidEnclosure k) l u x hx hx')
      (le_sigmoidDerivHi (sigmoidEnclosure k) l u x hx hx') hx hx'


-- =====================================  MAIN DEFINITION  ====================================== --

/-- That relaxation as a layer, one fit and one grid per neuron: the polynomial
activation layer over a float scalar, built rather than merely stated. -/
noncomputable def Layer.sigmoidPoly (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    Real.Layer (PolyZonotope 𝕋) n n :=
  Layer.activationPoly fun i => sigmoidPolyRelaxation k (c i) (dx i) (p i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
