import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.NN.Layers.Operations.PadCoeffs

/-!
# A polynomial relaxation read at a higher degree

An order pattern [1, Eq. 23] gives each neuron its own order while one activation layer
evaluates one coefficient list, so the fits meet at a common degree; nothing rounds and the error
is untouched. `k ≤ M` is a hypothesis of `padTo_sound` and not an argument here: padding is data,
and truncating would be data too, merely unsound.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A relaxation at a higher degree, which is how the neurons of one layer meet. -/
def PolyRelaxation.padTo (P : PolyRelaxation 𝕋 k) (M : ℕ) : PolyRelaxation 𝕋 M where
  coeffs l u := padCoeffs (P.coeffs l u) M
  error := P.error

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
