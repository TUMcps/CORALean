module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadRightNominalIff
public import CORALean.ContSet.HPolytope.Float.Theorems.PreimageAddImage

@[expose] public section

/-!
# Membership in `HPolytope.padRight`

The mirror statement for the right block.

## Inputs
* `P` – H-polytope
* `x` – point of length `n₁ + n₂`

## Hypotheses
* none

## Conclusion
* `x` lies in `P` padded on the right iff its right block lies in `P`
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

theorem HPolytope.mem_padRight_iff {P : HPolytope 𝕋 (Vec 𝕋 n₂)}
    {x : Vec ℝ (n₁ + n₂)} : -- --- CONCL ---
    x ∈ (HPolytope.padRight n₁ P).construct
      ↔ blockRight n₁ n₂ x ∈ P.construct := by -- --- PROOF ---
  -- the box is the padded box
  have hE : (HPolytope.padRight n₁ P).I_error.construct
      = blockPadRight n₁ n₂ '' P.I_error.construct := by
    ext y
    constructor
    -- a point of the padded box is the padded point of its own block
    · intro hy
      have hy' := Interval.mem_vec_iff.mp hy
      refine ⟨blockRight n₁ n₂ y, Interval.mem_vec_iff.mpr fun j => ?_, funext fun j => ?_⟩
      · have h := hy' (Fin.natAdd n₁ j)
        simp only [HPolytope.padRight, Fin.append_right] at h
        exact h
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · have h := hy' (Fin.castAdd n₂ i)
          simp only [HPolytope.padRight, Fin.append_left, toReal_zero] at h
          simp [blockPadRight, le_antisymm h.2 h.1]
        · simp [blockPadRight, blockRight]
    -- and a padded point of the box is in it
    · rintro ⟨e, he, rfl⟩
      refine Interval.mem_vec_iff.mpr fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [HPolytope.padRight, blockPadRight, toReal_zero]
      · simpa [HPolytope.padRight, blockPadRight] using Interval.mem_vec_iff.mp he i
  show x ∈ (HPolytope.padRight n₁ P).nominal.construct
    + (HPolytope.padRight n₁ P).I_error.construct ↔ _
  have hN : (HPolytope.padRight n₁ P).nominal.construct
      = blockRight n₁ n₂ ⁻¹' P.nominal.construct := by
    ext y
    exact HPolytope.mem_padRight_nominal_iff
  -- the preimage plus the padded box is the preimage of the sum
  have key := HPolytope.preimage_inter_add_image (blockRight n₁ n₂).toAddMonoidHom
    (blockPadRight n₁ n₂).toAddMonoidHom (fun e => blockRight_append 0 e)
    P.nominal.construct P.I_error.construct Set.univ (fun _ _ => by simp)
  simp only [Set.inter_univ] at key
  rw [hN, hE]
  have key' := congrArg (fun T : Set _ => x ∈ T) key
  simp only [LinearMap.toAddMonoidHom_coe, eq_iff_iff] at key'
  rw [key']
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
