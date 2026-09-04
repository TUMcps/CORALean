import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.and`

The constraint lists concatenate. Nothing is computed, so nothing rounds: the
intersection of two float halfspace descriptions is exact, as it is over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def HPolytope.and (P₁ P₂ : HPolytope 𝕋 n) : HPolytope 𝕋 n where
  m := P₁.m + P₂.m
  A := Fin.append P₁.A P₂.A
  b := Fin.append P₁.b P₂.b
  me := P₁.me + P₂.me
  Ae := Fin.append P₁.Ae P₂.Ae
  be := ⟨Fin.append P₁.be.inf P₂.be.inf, Fin.append P₁.be.sup P₂.be.sup⟩

variable [SoundFloatArithmetic 𝕋]

/-- A row of a concatenated constraint matrix, applied to a point. -/
theorem HPolytope.mulVec_append_left {m₁ m₂ : ℕ} (A₁ : Mat 𝕋 m₁ n) (A₂ : Mat 𝕋 m₂ n)
    (x : Vec ℝ n) (j : Fin m₁) :
    (toRealMat (Fin.append A₁ A₂) *ᵥ x) (Fin.castAdd m₂ j) = (toRealMat A₁ *ᵥ x) j := by
  show ∑ k, toReal (Fin.append A₁ A₂ (Fin.castAdd m₂ j) k) * x k = _
  rw [Fin.append_left]
  rfl

theorem HPolytope.mulVec_append_right {m₁ m₂ : ℕ} (A₁ : Mat 𝕋 m₁ n) (A₂ : Mat 𝕋 m₂ n)
    (x : Vec ℝ n) (j : Fin m₂) :
    (toRealMat (Fin.append A₁ A₂) *ᵥ x) (Fin.natAdd m₁ j) = (toRealMat A₂ *ᵥ x) j := by
  show ∑ k, toReal (Fin.append A₁ A₂ (Fin.natAdd m₁ j) k) * x k = _
  rw [Fin.append_right]
  rfl

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

theorem HPolytope.and_exact (P₁ P₂ : HPolytope 𝕋 n) :
    P₁.construct ∩ P₂.construct = (P₁.and P₂).construct :=
  Set.ext fun _ => HPolytope.mem_and_iff.symm

end CORALean.Float
