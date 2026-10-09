import CORALean.HybridDynamics.Parallel.Operations.ReachFloat
import CORALean.Global.Float.NoNaN

/-!
# `reachFloatChecked`, without a NaN

`reachFloat` followed by `checkNoNaN`: `none` where it is `none` or a float of its result is
a NaN. A `some` is the unchecked `some` (`reachFloatChecked_eq_some`), so whatever is proved
of `reachFloat` holds of it, and the NaN test that the trust base asks of the caller has
been made.
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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `reachFloat`, or `none` if a float of its result is a NaN. The location tuples carry no
floats. -/
def ParallelHybridAutomaton.reachFloatChecked
    (P : ParallelHybridAutomaton (Zonotope 𝕋) (HPolytope 𝕋) k L 𝕋 n m)
    (lift : ParallelHybridAutomaton.Lifting (Zonotope 𝕋) (HPolytope 𝕋) n m P.binds)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : ∀ i, L i)
    (X₀ : Zonotope 𝕋 (∑ i, n i)) : Option (List ((∀ i, L i) × Zonotope 𝕋 (∑ i, n i))) :=
  checkNoNaN (𝕋 := 𝕋) (P.reachFloat lift tFinal options K ℓ X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
