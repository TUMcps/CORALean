module

public import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `tFinal` – final time
* `options` – reach options
* `K` – jump depth
* `ℓ` – initial locations
* `X₀` – initial zonotope

## Output
* reach sets of the product, none on failure or NaN
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. The location tuples carry no
floats. -/
def ParallelHybridAutomaton.reachFloatChecked
    (P : ParallelHybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) n m)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope (Vec 𝕋 (∑ i, n i))) : Option (List ((∀ i, L i) × Zonotope (Vec 𝕋 (∑ i, n i)))) :=
  checkNoNaN (𝕋 := 𝕋) (P.reachFloat lift tFinal options K ℓ X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
