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

A plain `def`, and the last float layer to become one: every field stored is a
float expression and `Real.sigmoid` reaches nothing but the theorem beside it,
which is what splitting `PolyRelaxation.Sound` off `PolyRelaxation` bought.

The fit and the grid stay parameters, and neither owes a proof: any array of
floats is a fit, and a grid that fails `gridChecked` costs precision rather than
soundness. The scalar has no linear solve, so there is no default fit for this
file to prefer, and CORA's least squares would arrive here unverified anyway.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Last revision: 07-September-2026


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n N : ℕ}

/-- The `M` the sampling bound asks for: `Sigmoid`'s derivative bracket read
against the fit's own, one box at a time. -/
def sigmoidPolyDerivBound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (l u : 𝕋) : 𝕋 :=
  polyDerivBoundUp (c l u) (sigmoidDerivLo (sigmoidEnclosure k) l u)
    (sigmoidDerivHi (sigmoidEnclosure k) l u) l u

/-- `ofSampling` at the sigmoid: the derivative bound above, the fit `c` and the
grid `p`, `dx` free. Floats throughout, which is why it is a `def`. -/
def sigmoidPolyRelaxation (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofSampling (sigmoidEnclosure k) c (sigmoidPolyDerivBound k c) dx p

/-- Where `Real.sigmoid` appears, and the whole of what the assembly owes. -/
theorem sigmoidPolyRelaxation_sound (k : ℕ) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (dx : 𝕋 → 𝕋 → 𝕋)
    (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (sigmoidPolyRelaxation k c dx p).Sound Real.sigmoid :=
  PolyRelaxation.ofSampling_sound (E := sigmoidEnclosure k) (c := c)
    (M := sigmoidPolyDerivBound k c) (dx := dx) (p := p) (sigmoidEnclosure_sound k)
    Real.hasDerivAt_sigmoid fun l u x hx hx' => abs_sub_evalPolyDeriv_le
      (sigmoidDerivLo_le (sigmoidEnclosure_sound k) l u x hx hx')
      (le_sigmoidDerivHi (sigmoidEnclosure_sound k) l u x hx hx') hx hx'


-- =====================================  MAIN DEFINITION  ====================================== --

/-- That relaxation as a layer, one fit and one grid per neuron: the polynomial
activation layer over a float scalar, built rather than merely stated. -/
def Layer.sigmoidPoly (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    Real.Layer (PolyZonotope 𝕋) n n :=
  Layer.activationPoly fun i => sigmoidPolyRelaxation k (c i) (dx i) (p i)

/-- `Real.sigmoid` coordinatewise, which the layer itself never mentions. -/
theorem Layer.sigmoidPoly_sound (k : ℕ) (c : Fin n → 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (dx : Fin n → 𝕋 → 𝕋 → 𝕋) (p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) :
    (Layer.sigmoidPoly k c dx p).Sound fun x i => Real.sigmoid (x i) :=
  Layer.activationPoly_sound fun i => sigmoidPolyRelaxation_sound k (c i) (dx i) (p i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
