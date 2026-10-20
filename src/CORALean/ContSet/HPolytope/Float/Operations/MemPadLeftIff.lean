module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.PreimageAddImage

@[expose] public section

/-!
# Membership in `HPolytope.padLeft`

Membership of the padded polytope is membership of the block it came from,
both ways.

## Inputs
* `P` – H-polytope
* `x` – point of length `n₁ + n₂`

## Hypotheses
* none

## Conclusion
* `x` lies in `P` padded on the left iff its left block lies in `P`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)
--                16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_padLeft_iff {P : HPolytope 𝕋 (Vec 𝕋 n₁)}
    {x : Vec ℝ (n₁ + n₂)} : -- --- CONCL ---
    x ∈ (P.padLeft n₂).construct ↔ blockLeft n₁ n₂ x ∈ P.construct := by -- --- PROOF ---
  -- the box is the padded box
  have hE : (P.padLeft n₂).I_error.construct = blockPadLeft n₁ n₂ '' P.I_error.construct := by
    ext y
    constructor
    -- a point of the padded box is the padded point of its own block
    · intro hy
      have hy' := Interval.mem_vec_iff.mp hy
      refine ⟨blockLeft n₁ n₂ y, Interval.mem_vec_iff.mpr fun j => ?_, funext fun j => ?_⟩
      · have h := hy' (Fin.castAdd n₂ j)
        simp only [HPolytope.padLeft, Fin.append_left] at h
        exact h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [blockPadLeft, blockLeft]
        · have h := hy' (Fin.natAdd n₁ i)
          simp only [HPolytope.padLeft, Fin.append_right, toReal_zero] at h
          simp [blockPadLeft, le_antisymm h.2 h.1]
    -- and a padded point of the box is in it
    · rintro ⟨e, he, rfl⟩
      refine Interval.mem_vec_iff.mpr fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [HPolytope.padLeft, blockPadLeft] using Interval.mem_vec_iff.mp he i
      · simp [HPolytope.padLeft, blockPadLeft, toReal_zero]
  show x ∈ (P.padLeft n₂).nominal.construct + (P.padLeft n₂).I_error.construct ↔ _
  have hN : (P.padLeft n₂).nominal.construct = blockLeft n₁ n₂ ⁻¹' P.nominal.construct := by
    ext y
    exact HPolytope.mem_padLeft_nominal_iff
  -- the preimage plus the padded box is the preimage of the sum
  have key := HPolytope.preimage_inter_add_image (blockLeft n₁ n₂).toAddMonoidHom
    (blockPadLeft n₁ n₂).toAddMonoidHom (fun e => blockLeft_append e 0)
    P.nominal.construct P.I_error.construct Set.univ (fun _ _ => by simp)
  simp only [Set.inter_univ] at key
  rw [hN, hE]
  have key' := congrArg (fun T : Set _ => x ∈ T) key
  simp only [LinearMap.toAddMonoidHom_coe, eq_iff_iff] at key'
  rw [key']
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
