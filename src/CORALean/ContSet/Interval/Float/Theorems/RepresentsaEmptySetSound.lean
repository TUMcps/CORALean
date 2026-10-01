import CORALean.ContSet.Interval.Float.Operations.RepresentsaEmptySet

/-!
# `Interval.representsa_emptySet` is sound

A `true` answer names a coordinate with `toReal sup < toReal inf`, which no point satisfies.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.representsa_emptySet_sound {I : Interval (Vec 𝕋 n)}
    (h : I.representsa_emptySet = true) : I.construct = ∅ := by -- --- PROOF ---
  simp only [Interval.representsa_emptySet, List.any_eq_true, List.mem_finRange, true_and] at h
  obtain ⟨j, hj⟩ := h
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have h₁ : toReal (I.inf j) ≤ x j := (hx j).1
  have h₂ : x j ≤ toReal (I.sup j) := (hx j).2
  linarith [toReal_lt_of_ltStrict hj]


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
