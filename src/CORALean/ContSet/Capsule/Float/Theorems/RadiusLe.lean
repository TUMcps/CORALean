module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Real.Theorems.NormSubCenterLe

@[expose] public section

/-!
# Every point of a float capsule is within `radius` of the nominal center

The exact layer's `norm₂_sub_center_le` at the nominal capsule, with `√(Σ g²)` replaced by its
rounded-up `normUp` and the sum by `addUp`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.radius_le (k : ℕ) (C : Capsule 𝕋 n) {x : Vec ℝ n} (hx : x ∈ C.construct) :
    ‖x - toRealVec C.c‖₂ ≤ toReal (C.radius k) := by -- --- PROOF ---
  have h₁ := CORALean.Real.Capsule.norm₂_sub_center_le (C := C.nominal) hx
  have h₂ : ‖toRealVec C.g‖₂ ≤ toReal (normUp k C.g) :=
    norm₂_le_normUp k fun j => le_rfl
  have h₃ := add_le_addUp (normUp k C.g) C.r
  change ‖x - toRealVec C.c‖₂ ≤ ‖toRealVec C.g‖₂ + toReal C.r at h₁
  have h₄ : toReal (C.radius k) = toReal (addUp (normUp k C.g) C.r) := rfl
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
