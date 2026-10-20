module

public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# Membership in the nominal part of `HPolytope.stackRows`, over a floating-point scalar

Membership splits with the rows, each half read on the nominal part it came from.

## Inputs
* `P₁` – H-polytope
* `P₂` – H-polytope
* `x` – point of length `n`

## Hypotheses
* none

## Conclusion
* `x` lies in the nominal part of the stacked rows iff it lies in both nominal parts
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- membership splits with the rows, each half read on the nominal part it came from
theorem HPolytope.mem_stackRows_nominal_iff {P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ (P₁.stackRows P₂).nominal.construct
      ↔ x ∈ P₁.nominal.construct ∧ x ∈ P₂.nominal.construct := by -- --- PROOF ---
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun i => ?_, fun i => ?_⟩
    · have h := hle (Fin.castAdd P₂.m i)
      simp only [HPolytope.stackRows, HPolytope.mulVec_append_left, Fin.append_left] at h
      exact h
    · have h := heq (Fin.castAdd P₂.me i)
      simp only [HPolytope.stackRows, HPolytope.mulVec_append_left, Fin.append_left] at h
      exact h
    · have h := hle (Fin.natAdd P₁.m i)
      simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right] at h
      exact h
    · have h := heq (Fin.natAdd P₁.me i)
      simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right] at h
      exact h
  -- back: the two memberships are the two halves of one row list
  · rintro ⟨⟨hle₁, heq₁⟩, hle₂, heq₂⟩
    refine ⟨?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.stackRows, HPolytope.mulVec_append_left, Fin.append_left]
        exact hle₁ i
      · simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right]
        exact hle₂ i
    · refine Fin.addCases (fun i => ?_) fun i => ?_
      · simp only [HPolytope.stackRows, HPolytope.mulVec_append_left, Fin.append_left]
        exact heq₁ i
      · simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right]
        exact heq₂ i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
