module

public import CORALean.NN.Layers.Operations.FitHi
public import CORALean.NN.Layers.Operations.FitLo
public import CORALean.NN.Layers.Operations.PolyRelaxationOfBracket

@[expose] public section

/-!
# The polynomial relaxation a fit and a checked grid buy

CORA's `computeApproxError` [1] assembled from stored pieces: the grid certified rather than
computed, the fit enclosed by `evalPolyDown`/`evalPolyUp`, the activation by an `Enclosure`, and
the recentering paying for its own rounding in `ofBracket`. The fit `c` owes nothing — any array
of stored values, a least-squares solve, a Taylor expansion or a guess — and decides precision
alone. All four arguments are data; `ofSampling_encloses` is what they are worth.

## Inputs
* `E` – enclosure of the activation
* `c` – fit coefficients for each box
* `M` – derivative bound for each box
* `dx` – grid spacing for each box
* `p` – proposed sample grid for each box

## Output
* polynomial relaxation from the fit and its checked grid

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
