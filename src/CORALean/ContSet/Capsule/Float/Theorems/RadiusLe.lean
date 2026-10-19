module

public import CORALean.ContSet.Capsule.Float.Theorems.Norm2LeErrorNorm
public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Real.Theorems.NormSubCenterLe
public import CORALean.ContSet.Capsule.Float.Theorems.Basic

@[expose] public section

/-!
# Every point of a float capsule is within `radius` of the nominal center

The exact layer's `norm₂_sub_center_le` at the nominal capsule, with `√(Σ g²)` replaced by its
rounded-up `normUp` and the sum by `addUp`, and the error box's point within `errorNorm` of the
origin by the triangle inequality.

## Inputs
* `k` – Newton steps for sqrt
* `C` – capsule
* `x` – real point

## Hypotheses
* `hx` – `x` lies in the capsule

## Conclusion
* `x` is within `radius` of the nominal center
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.radius_le (k : ℕ) (C : Capsule 𝕋 n) {x : Vec ℝ n} (hx : x ∈ C.construct) :
    ‖x - toRealVec C.c‖₂ ≤ toReal (C.radius k) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := hx
  have h₁ := CORALean.Real.Capsule.norm₂_sub_center_le (C := C.nominal) hy
  have h₂ : ‖toRealVec C.g‖₂ ≤ toReal (normUp k C.g) :=
    norm₂_le_normUp k fun j => le_rfl
  have h₃ := add_le_addUp (normUp k C.g) C.r
  have h₄ := add_le_addUp (addUp (normUp k C.g) C.r) (C.errorNorm k)
  have h₅ := Capsule.norm₂_le_errorNorm k C he
  change ‖y - toRealVec C.c‖₂ ≤ ‖toRealVec C.g‖₂ + toReal C.r at h₁
  have h₆ : ‖y + e - toRealVec C.c‖₂ ≤ ‖y - toRealVec C.c‖₂ + ‖e‖₂ := by
    rw [show y + e - toRealVec C.c = (y - toRealVec C.c) + e by abel]
    exact norm₂_add_le _ _
  show _ ≤ toReal (addUp (addUp (normUp k C.g) C.r) (C.errorNorm k))
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
