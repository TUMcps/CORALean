import CORALean.ContSet.HPolytope.Float.Operations.Eqs

/-!
# Membership in `HPolytope.eqs`, over a floating-point scalar
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_eqs_iff {Ae : Mat 𝕋 q n} {be : Interval (Vec 𝕋 q)} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔
      ∀ i, toReal (be.inf i) ≤ (toRealMat Ae *ᵥ x) i
           ∧ (toRealMat Ae *ᵥ x) i ≤ toReal (be.sup i) :=
  ⟨fun h => (HPolytope.mem_construct_iff.mp h).2,
   fun h => HPolytope.mem_construct_iff.mpr ⟨fun i => i.elim0, h⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
