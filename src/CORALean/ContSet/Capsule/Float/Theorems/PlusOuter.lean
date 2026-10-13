import CORALean.ContSet.Capsule.Float.Operations.Plus
import CORALean.ContSet.Capsule.Real.Theorems.PlusOuterKeepLeft
import CORALean.ContSet.Capsule.Real.Theorems.ConstructSubsetOfDistLe

/-!
# `Capsule.plus` encloses the sum

The exact layer's `plus_outer_keep_left` gives the sum inside the capsule that keeps one
generator, with the centre added exactly. `construct_subset_of_dist_le` moves it to the stored
capsule: the centre is `‖c₁ + c₂ - c‖₂` away, which `rounding` bounds, and the generator is the
same.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored centre is within `rounding` of the exact sum of the stored centres. -/
private theorem aux_centre_gap_le (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) :
    ‖(toRealVec C₁.c + toRealVec C₂.c) - toRealVec (fun i => addDown (C₁.c i) (C₂.c i))‖₂ ≤
      toReal (normUp k fun i =>
        subUp (addUp (C₁.c i) (C₂.c i)) (addDown (C₁.c i) (C₂.c i))) := by -- --- PROOF ---
  refine norm₂_le_normUp k fun j => ?_
  have h₁ := addDown_le_add (C₁.c j) (C₂.c j)
  have h₂ := add_le_addUp (C₁.c j) (C₂.c j)
  have h₃ := sub_le_subUp (addUp (C₁.c j) (C₂.c j)) (addDown (C₁.c j) (C₂.c j))
  have h₀ : 0 ≤ toReal (C₁.c j) + toReal (C₂.c j) - toReal (addDown (C₁.c j) (C₂.c j)) := by
    linarith
  show |toReal (C₁.c j) + toReal (C₂.c j) - toReal (addDown (C₁.c j) (C₂.c j))| ≤ _
  rw [abs_of_nonneg h₀, abs_of_nonneg (by linarith)]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.plus_outer (k : ℕ) (C₁ C₂ : Capsule 𝕋 n) :
    C₁.construct + C₂.construct ⊆ (C₁.plus k C₂).construct := by -- --- PROOF ---
  rintro _ ⟨x₁, h₁, x₂, h₂, rfl⟩
  -- the rounding of the centre, and the generators' lengths
  have hr := aux_centre_gap_le k C₁ C₂
  have hg₁ : ‖toRealVec C₁.g‖₂ ≤ toReal (normUp k C₁.g) := norm₂_le_normUp k fun j => le_rfl
  have hg₂ : ‖toRealVec C₂.g‖₂ ≤ toReal (normUp k C₂.g) := norm₂_le_normUp k fun j => le_rfl
  have s₁ := add_le_addUp C₁.r C₂.r
  unfold Capsule.plus
  dsimp only
  split_ifs
  · -- the first generator is kept: the exact layer's keep-left capsule, then the distance lemma
    have hK := CORALean.Real.Capsule.plus_outer_keep_left C₁.nominal C₂.nominal h₁ h₂
    refine CORALean.Real.Capsule.construct_subset_of_dist_le (C := ⟨_, _, _⟩) ?_ hK
    have s₂ := add_le_addUp (addUp C₁.r C₂.r) (normUp k C₂.g)
    have s₃ := add_le_addUp (addUp (addUp C₁.r C₂.r) (normUp k C₂.g))
      (normUp k fun i => subUp (addUp (C₁.c i) (C₂.c i)) (addDown (C₁.c i) (C₂.c i)))
    show ‖(toRealVec C₁.c + toRealVec C₂.c) - toRealVec (fun i => addDown (C₁.c i) (C₂.c i))‖₂ +
        ‖toRealVec C₁.g - toRealVec C₁.g‖₂ + (toReal C₁.r + toReal C₂.r + ‖toRealVec C₂.g‖₂) ≤
      toReal (addUp (addUp (addUp C₁.r C₂.r) (normUp k C₂.g))
        (normUp k fun i => subUp (addUp (C₁.c i) (C₂.c i)) (addDown (C₁.c i) (C₂.c i))))
    rw [sub_self, CORALean.norm₂_zero]
    linarith
  · -- the second generator is kept: the same with the operands swapped, and the sum commuted
    have hK := CORALean.Real.Capsule.plus_outer_keep_left C₂.nominal C₁.nominal h₂ h₁
    rw [add_comm x₂ x₁] at hK
    refine CORALean.Real.Capsule.construct_subset_of_dist_le (C := ⟨_, _, _⟩) ?_ hK
    have s₂ := add_le_addUp (addUp C₁.r C₂.r) (normUp k C₁.g)
    have s₃ := add_le_addUp (addUp (addUp C₁.r C₂.r) (normUp k C₁.g))
      (normUp k fun i => subUp (addUp (C₁.c i) (C₂.c i)) (addDown (C₁.c i) (C₂.c i)))
    show ‖(toRealVec C₂.c + toRealVec C₁.c) - toRealVec (fun i => addDown (C₁.c i) (C₂.c i))‖₂ +
        ‖toRealVec C₂.g - toRealVec C₂.g‖₂ + (toReal C₂.r + toReal C₁.r + ‖toRealVec C₁.g‖₂) ≤
      toReal (addUp (addUp (addUp C₁.r C₂.r) (normUp k C₁.g))
        (normUp k fun i => subUp (addUp (C₁.c i) (C₂.c i)) (addDown (C₁.c i) (C₂.c i))))
    rw [sub_self, CORALean.norm₂_zero, add_comm (toRealVec C₂.c)]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
