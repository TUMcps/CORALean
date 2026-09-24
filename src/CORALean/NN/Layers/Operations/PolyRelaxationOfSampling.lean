import CORALean.NN.Layers.Operations.FitHi
import CORALean.NN.Layers.Operations.FitLo
import CORALean.NN.Layers.Operations.PolyRelaxationOfBracket

/-!
# The polynomial relaxation a fit and a checked grid buy

CORA's `computeApproxError` [1] assembled from stored pieces: the grid certified rather than
computed, the fit enclosed by `evalPolyDown`/`evalPolyUp`, the activation by an `Enclosure`, and
the recentring paying for its own rounding in `ofBracket`. The fit `c` owes nothing — any array
of stored values, a least-squares solve, a Taylor expansion or a guess — and decides precision
alone. All four arguments are data; `ofSampling_sound` is what they are worth.

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

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The relaxation a fit, a derivative bound and a proposed grid buy. -/
def PolyRelaxation.ofSampling (E : Enclosure 𝕋) (c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋)
    (M dx : 𝕋 → 𝕋 → 𝕋) (p : 𝕋 → 𝕋 → Fin (N + 1) → 𝕋) : PolyRelaxation 𝕋 m :=
  PolyRelaxation.ofBracket c (fitLo E c M dx p) (fitHi E c M dx p)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
