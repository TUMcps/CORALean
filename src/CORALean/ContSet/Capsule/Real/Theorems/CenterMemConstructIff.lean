module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# A capsule holds its center exactly when its radius is nonnegative

CORA's `center` is the field `c`. It lies in the capsule at the segment parameter `t = 0`,
where the distance to it is `Real.sqrt 0 = 0`, so the only thing that can exclude it is a
negative radius, which denotes `∅`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.center_mem_construct_iff (C : Capsule n) :
    C.c ∈ C.construct ↔ 0 ≤ C.r := by -- --- PROOF ---
  constructor
  · rintro ⟨t, -, h⟩
    exact le_trans (Real.sqrt_nonneg _) h
  · intro hr
    refine ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, ?_⟩
    simpa using hr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
