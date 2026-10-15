module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloatChecked
public import CORALean.Global.Float.NoNaN

@[expose] public section

/-!
# A checked `reachFloat` that returns a result returns the unchecked one

`reachFloatChecked` is `reachFloat` followed by `checkNoNaN`, so a `some` of it is the
unchecked `some`, and none of its floats is a NaN. Whatever is proved of `reachFloat` is
proved of the checked result, which has passed the NaN test as well.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.reachFloatChecked_eq_some
    (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ) (options : NeurNetContrSys.ReachOptions 𝕋)
    {R : Zonotope (Vec 𝕋 n)} (h : sys.reachFloatChecked params options = some R) :
    sys.reachFloat params options = R ∧ noNaN (𝕋 := 𝕋) R = true := by -- --- PROOF ---
  obtain ⟨rfl, hx⟩ := ifNoNaN_eq_some h
  exact ⟨rfl, hx⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
