module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZono
public import CORALean.ContDynamics.LinearSys.Definitions.VerifyZonoGenSet
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `LinearSys/Definitions`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q : ℕ}


-- ===============================  `LinearSys.VerifyZono.toSet`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `{c + y + e | y ∈ ⟨0, G⟩, |eᵢ| ≤ rᵢ}`: every float of the zonotope `Z` read as a real. -/
def LinearSys.VerifyZono.toSet (Z : LinearSys.VerifyZono 𝕋 q) : Set (Vec ℝ q) :=
  {x | ∃ y ∈ LinearSys.verifyZonoGenSet (Z.G.map toRealVec), ∃ e : Vec ℝ q,
    (∀ i, |e i| ≤ toReal (Z.r i)) ∧ x = toRealVec Z.c + y + e}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
