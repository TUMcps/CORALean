module

public import CORALean.ContSet.HPolytope.Float.Operations.ContainsOrigin
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff

@[expose] public section

/-!
# `HPolytope.containsOrigin` is sound

Every row reads the origin as `0`: an inequality's bound with its slack is at least the rounded-down
sum the test certified nonnegative, and an equality's right-hand side is within its slack of `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A passed test puts the origin in the nominal part. -/
theorem HPolytope.containsOrigin_sound {P : HPolytope 𝕋 (Vec 𝕋 n)}
    (h : P.containsOrigin = true) : (0 : Vec ℝ n) ∈ P.nominal.construct := by -- --- PROOF ---
  simp only [HPolytope.containsOrigin, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨hA, hE⟩ := h
  refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  -- an inequality reads `0`, at most its bound with its slack
  · have h0 := toReal_le_of_le (hA i)
    have h1 := addDown_le_add (P.b i) (absolute (P.b_error i))
    rw [toReal_zero] at h0
    rw [toReal_absolute] at h1
    rw [Matrix.mulVec_zero, Pi.zero_apply]
    linarith
  -- an equality reads `0`, within its slack of the right-hand side
  · have h0 := toReal_le_of_le (hE i)
    rw [toReal_absolute, toReal_absolute] at h0
    rw [Matrix.mulVec_zero, Pi.zero_apply, zero_sub, abs_neg]
    exact h0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
