module

public import CORALean.ContSet.Interval.Float.Operations.ProjectHighDim
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound

@[expose] public section

/-!
# `Interval.projectHighDim_` contains the zero-padded points

For injective `proj`: `Fin.find` recovers the index of a coordinate in the range, and every other
coordinate is `0`. A box certified empty has no points to pad.

## Inputs
* `I` – interval box
* `proj` – coordinate embedding

## Hypotheses
* `hproj` – embedding injective

## Conclusion
* every zero-padded point lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.projectHighDim_outer (I : Interval (Vec 𝕋 m)) (proj : Fin m → Fin N)
    (hproj : Function.Injective proj) : -- --- CONCL ---
    (fun x => Function.extend proj x 0) '' I.construct ⊆
      (I.projectHighDim_ N proj).construct := by -- --- PROOF ---
  rintro _ ⟨x, hx, rfl⟩ j
  -- a box certified empty has no member to pad
  by_cases hemp : I.representsa_emptySet = true
  · have h := Interval.representsa_emptySet_sound hemp
    rw [h] at hx
    exact hx.elim
  · rw [Interval.projectHighDim_, if_neg hemp]
    -- a coordinate in the range of `proj` reads the member's, any other reads `0`
    by_cases h : ∃ k, proj k = j
    · obtain ⟨k, rfl⟩ := h
      have hf : Fin.find (fun k' => proj k' = proj k) ⟨k, rfl⟩ = k :=
        hproj (Fin.find_spec (p := fun k' => proj k' = proj k) ⟨k, rfl⟩)
      have hx' : toReal (I.inf k) ≤ x k ∧ x k ≤ toReal (I.sup k) := hx k
      -- lower bound, then upper bound
      refine ⟨?_, ?_⟩
      · show toReal (if h : ∃ k', proj k' = proj k then _ else _) ≤
          Function.extend proj x 0 (proj k)
        rw [dif_pos ⟨k, rfl⟩, hf, hproj.extend_apply]
        exact hx'.1
      · show Function.extend proj x 0 (proj k) ≤
          toReal (if h : ∃ k', proj k' = proj k then _ else _)
        rw [dif_pos ⟨k, rfl⟩, hf, hproj.extend_apply]
        exact hx'.2
    · refine ⟨?_, ?_⟩
      · show toReal (if h : ∃ k', proj k' = j then _ else _) ≤ Function.extend proj x 0 j
        rw [dif_neg h, toReal_zero, Function.extend_apply' _ _ _ h]
        exact le_refl _
      · show Function.extend proj x 0 j ≤ toReal (if h : ∃ k', proj k' = j then _ else _)
        rw [dif_neg h, toReal_zero, Function.extend_apply' _ _ _ h]
        exact le_refl _


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
