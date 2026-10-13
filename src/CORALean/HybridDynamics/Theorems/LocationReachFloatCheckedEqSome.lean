import CORALean.HybridDynamics.Operations.LocationReachFloatChecked

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {G : ℕ → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.reachFloatChecked_eq_some
    (ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n) (tFinal : ℚ)
    (options : LinearSys.ReachOptions 𝕋) (X₀ : Zonotope (Vec 𝕋 n))
    {Rs : (List (Zonotope (Vec 𝕋 n)))}
    (h : ℓ.reachFloatChecked tFinal options X₀ = some Rs) :
    ℓ.reachFloat tFinal options X₀ = some Rs ∧ noNaN (𝕋 := 𝕋) Rs = true :=
  checkNoNaN_eq_some h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
