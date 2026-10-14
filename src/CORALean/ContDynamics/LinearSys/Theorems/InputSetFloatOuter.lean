module

public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

@[expose] public section

/-!
# `inputSetFloat` holds every input of the full equation

For every `u ∈ U`, the system's own input term `B u + c` lies in `inputSetFloat U`: `B u` in
the product `B U`, `c` in the point `c`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.inputSetFloat_outer (sys : LinearSys 𝕋 n) (U : Zonotope (Vec 𝕋 sys.m)) :
    (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) '' U.construct ⊆
      (sys.inputSetFloat U).construct := by -- --- PROOF ---
  rintro _ ⟨u, hu, rfl⟩
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) sys.B U
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hu)))
    (show _ ∈ (Zonotope.point sys.c).construct by rw [Zonotope.construct_point]; rfl))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
