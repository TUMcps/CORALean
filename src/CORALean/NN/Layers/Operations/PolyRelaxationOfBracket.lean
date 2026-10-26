module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Operations.BracketError
public import CORALean.NN.Layers.Operations.ShiftConst

@[expose] public section

/-!
# A polynomial relaxation out of a bracket, recentered

`computeApproxError`'s last step [1]: a bracket for `σ - p` over the box, its two ends averaged
into the constant coefficient, and what is left is a radius. The bracket is a hypothesis of
`ofBracket_isSound` and not an argument here, which keeps `σ` out of the data.

## Inputs
* `c` – fit coefficients for each box
* `lo` – lower end of the error bracket
* `hi` – upper end of the error bracket

## Output
* polynomial relaxation recentered on the error bracket

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A relaxation out of any bracket for `σ` minus the fit, recentered. -/
def PolyRelaxation.ofBracket (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋) (lo hi : 𝕋 → 𝕋 → 𝕋) :
    PolyRelaxation 𝕋 m where
  coeffs l u := shiftConst (c l u) (bracketShift (lo l u) (hi l u))
  error l u := bracketError (c l u 0) (lo l u) (hi l u)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
