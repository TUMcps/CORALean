module

public import CORALean.ContDynamics.LinearSys.Operations.ManualStepFloat

@[expose] public section

/-!
# `Alg. 1` lines 4-11 in floats: the loop

`manualRun`, [1, Alg. 1] lines 4-11, computed in `𝕋`: iterate `manualStepFloat` `k` times
from a state, collecting each iteration's `R̂(τ_k)`. `none` as soon as one iteration is.

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `Δt` – float step length
* `η` – Taylor order
* `ρ` – zonotope order

## Output
* windows of the iterations from a given state, if all succeed

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-11: the windows `R̂(τ_k), …, R̂(τ_{k+K-1})` of `K` iterations from `s`. -/
def LinearSys.manualRunFloat (sys : LinearSys 𝕋 n) (X₀ V : Zonotope (Vec 𝕋 n)) (Δt : 𝕋)
    (η ρ : ℕ) : ℕ → LinearSys.ManualStateFloat 𝕋 n → Option (List (Zonotope (Vec 𝕋 n)))
  | 0, _ => some []
  | K + 1, s => do
    let (s', Rτk) ← sys.manualStepFloat X₀ V Δt η ρ s               -- 5.-11. one iteration
    let Rs ← sys.manualRunFloat X₀ V Δt η ρ K s'                     -- 4. the rest of the loop
    pure (Rτk :: Rs)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
