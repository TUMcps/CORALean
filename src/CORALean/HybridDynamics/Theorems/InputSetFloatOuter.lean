module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.HybridDynamics.Operations.InputSetFloat

@[expose] public section

/-!
# `Location.inputSetFloat` holds every combined input

For every input `u ∈ U` and disturbance `w ∈ W` of a location at float zonotopes, the combined
input `B u + c + E w` lies in `inputSetFloat`: `B u + c` in `LinearSys.inputSetFloat U`
(`inputSetFloat_outer`), `E w` in the float product `E W`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix ContSet

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Location.inputSetFloat_outer (ℓ : Location 𝒵[𝕋] G L 𝕋 n) {u : Vec ℝ ℓ.dynamics.m}
    {w : Vec ℝ ℓ.dynamics.r} (hu : u ∈ construct ℓ.U) (hw : w ∈ construct ℓ.W) :
    Scalar.toRealMat ℓ.dynamics.B *ᵥ u + Scalar.toRealVec ℓ.dynamics.c +
      Scalar.toRealMat ℓ.dynamics.E *ᵥ w ∈ construct ℓ.inputSetFloat := by
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (ℓ.dynamics.inputSetFloat_outer ℓ.U ⟨u, hu, rfl⟩)
    (Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) ℓ.dynamics.E ℓ.W
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
