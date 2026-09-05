import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendRight
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# Membership in `HPolytope.and`, over a floating-point scalar

Membership splits with the rows, each half read on the polytope it came from.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

-- membership splits with the rows, each half read on the polytope it came from
theorem HPolytope.mem_and_iff {P₁ P₂ : HPolytope 𝕋 n} {x : Vec ℝ n} :
    x ∈ (P₁.and P₂).construct ↔ x ∈ P₁.construct ∧ x ∈ P₂.construct := by
  constructor
  · intro hmem
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hmem
    refine ⟨HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩,
      HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ?_⟩⟩
    · have h := hle (Fin.castAdd P₂.m i)
      simp only [HPolytope.and, HPolytope.mulVec_append_left, Fin.append_left] at h
      exact h
    · have h := heq (Fin.castAdd P₂.me i)
      simp only [HPolytope.and, HPolytope.mulVec_append_left, Fin.append_left] at h
      exact h
    · have h := hle (Fin.natAdd P₁.m i)
      simp only [HPolytope.and, HPolytope.mulVec_append_right, Fin.append_right] at h
      exact h
    · have h := heq (Fin.natAdd P₁.me i)
      simp only [HPolytope.and, HPolytope.mulVec_append_right, Fin.append_right] at h
      exact h
  -- back: the two memberships are the two halves of one row list
  · rintro ⟨h₁, h₂⟩
    obtain ⟨hle₁, heq₁⟩ := HPolytope.mem_construct_iff.mp h₁
    obtain ⟨hle₂, heq₂⟩ := HPolytope.mem_construct_iff.mp h₂
    refine HPolytope.mem_construct_iff.mpr ⟨?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.and, HPolytope.mulVec_append_left, Fin.append_left]
        exact hle₁ i
      · simp only [HPolytope.and, HPolytope.mulVec_append_right, Fin.append_right]
        exact hle₂ i
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.and, HPolytope.mulVec_append_left, Fin.append_left]
        exact heq₁ i
      · simp only [HPolytope.and, HPolytope.mulVec_append_right, Fin.append_right]
        exact heq₂ i

end CORALean.Float
