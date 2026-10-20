module

public import CORALean.HybridDynamics.Parallel.Operations.ReachFloatChecked
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.

## Inputs
* `P` – parallel automaton
* `lift` – lifting
* `tFinal` – final time
* `options` – reach options
* `K` – jump depth
* `ℓ` – initial locations
* `X₀` – initial zonotope

## Hypotheses
* none

## Conclusion
* a checked result is the unchecked one without NaN
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.reachFloatChecked_eq_some
    (P : ParallelHybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) n m) (tFinal : ℚ)
    (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope (Vec 𝕋 (∑ i, n i))) :
    ∀ Rs ∈ P.reachFloatChecked lift tFinal options K ℓ X₀,
      P.reachFloat lift tFinal options K ℓ X₀ = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true := fun _ h =>
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
