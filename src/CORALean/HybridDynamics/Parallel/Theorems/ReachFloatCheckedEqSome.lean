import CORALean.HybridDynamics.Parallel.Operations.ReachFloatChecked
import CORALean.Global.Float.NoNaN

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {k m : ℕ} {n : Fin k → ℕ} {L : Fin k → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ParallelHybridAutomaton.reachFloatChecked_eq_some
    (P : ParallelHybridAutomaton (Zonotope 𝕋) (HPolytope 𝕋) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting (Zonotope 𝕋) (HPolytope 𝕋) n m P.binds)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope 𝕋 (∑ i, n i)) {Rs : List ((∀ i, L i) × Zonotope 𝕋 (∑ i, n i))}
    (h : P.reachFloatChecked lift tFinal options K ℓ X₀ = some Rs) :
    P.reachFloat lift tFinal options K ℓ X₀ = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
