module

public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.HybridDynamics.Definitions.Location

@[expose] public section

/-!
# `Location.inputSetFloat`

`Location.inputSet` at float zonotopes: `LinearSys.inputSetFloat`'s `B U ⊕ c`, the system's `B`
and `c` at the location's `U`, plus `E W`, the disturbances CORA's `canonicalForm` [1] folds into
the input. At `W` a point zonotope of `0`, `E W` adds no generator. Soundness is
`inputSetFloat_outer`.

## References

* [1] `contDynamics/@linearSys/canonicalForm.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `B U ⊕ c ⊕ E W`, the input set of the canonical form, in the state space. -/
def Location.inputSetFloat (ℓ : Location 𝒵[𝕋] G L 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  ℓ.dynamics.inputSetFloat ℓ.U ⊞ Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ℓ.dynamics.E ℓ.W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
