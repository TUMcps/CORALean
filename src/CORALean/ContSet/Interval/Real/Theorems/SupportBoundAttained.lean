module

public import CORALean.ContSet.Interval.Real.Theorems.SupportBoundEntrywiseAttained
public import CORALean.ContSet.Interval.Real.Operations.SupportBound

@[expose] public section

/-!
# A nonempty box's support bound over `Vec ℝ n` is its support function

`Interval.supportBoundEntrywise_attained` at the ambient type `Vec ℝ n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.supportBound_attained {n : ℕ} (I : Interval (Vec ℝ n))
    (c : Vec ℝ n →ₗ[ℝ] ℝ) (hI : I.IsNonempty) :
    ∃ x ∈ I.construct, c x = (I.supportBound c).val :=
  Interval.supportBoundEntrywise_attained I c hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
