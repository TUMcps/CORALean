module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Operations.PadCoeffs

@[expose] public section

/-!
# A polynomial relaxation read at a higher degree

An order pattern [1, Eq. 23] gives each neuron its own order while one activation layer
evaluates one coefficient list, so the fits meet at a common degree; nothing rounds and the error
is untouched. `k ≤ M` is a hypothesis of `padTo_sound` and not an argument here: padding is data,
and truncating would be data too, merely unsound.

## Inputs
* `P` – polynomial relaxation
* `M` – higher degree

## Output
* the relaxation read at the higher degree

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
