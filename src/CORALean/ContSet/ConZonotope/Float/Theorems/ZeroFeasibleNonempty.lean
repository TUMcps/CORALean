module

public import CORALean.ContSet.ConZonotope.Float.Operations.ZeroFeasible
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# A constrained zonotope that passes `zeroFeasible` is nonempty

Coefficients `0` meet the unit box, and meet every row because each bound is at least `0` and
each equality's right-hand side is `0`; the point they name is the center.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zeroFeasible_nonempty {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (h : cZ.zeroFeasible = true) :
    (nominalSet cZ).Nonempty := by -- --- PROOF ---
  simp only [ConZonotope.zeroFeasible, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, true_implies, Bool.and_eq_true] at h
  obtain ⟨hA, hE⟩ := h
  refine ⟨fun i => toReal (cZ.c i), ConZonotope.mem_nominalSet_iff.mpr
    ⟨0, fun j => by simp, HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩,
      fun i => by simp⟩⟩
  · rw [Matrix.mulVec_zero, Pi.zero_apply]
    have h0 := toReal_le_of_le (hA i)
    rw [toReal_zero] at h0
    linarith [abs_nonneg (toReal (cZ.P.b_error i))]
  · rw [Matrix.mulVec_zero]
    have h0 := le_antisymm (toReal_le_of_le (hE i).2) (toReal_le_of_le (hE i).1)
    rw [toReal_zero] at h0
    rw [Pi.zero_apply, ← h0, sub_self, abs_zero]
    exact abs_nonneg _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
