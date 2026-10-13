module

public import CORALean.HybridDynamics.Operations.ReachFloatChecked
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.reachFloatChecked_eq_some
    (HA : HybridAutomaton (fun k => Zonotope (Vec 𝕋 k)) (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (tFinal : ℚ) (options : LinearSys.ReachOptions 𝕋) (K : ℕ) (ℓ : L) (X₀ : Zonotope (Vec 𝕋 n))
    {Rs : List (L × Zonotope (Vec 𝕋 n))}
    (h : HA.reachFloatChecked tFinal options K ℓ X₀ = some Rs) :
    HA.reachFloat tFinal options K ℓ X₀ = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
