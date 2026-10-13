import CORALean.ContSet.Capsule.Real.Capsule
import CORALean.Global.EuclideanNorm

/-!
# A point of a capsule, in the Euclidean norm

`construct` states the bound as a square root of a sum; this is the same statement in `‖·‖₂`,
at the offset `p - c` from the centre.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.mem_construct_iff_norm₂ (C : Capsule n) (p : Vec ℝ n) :
    p ∈ C.construct ↔ ∃ t ∈ Set.Icc (-1 : ℝ) 1, ‖(p - C.c) - t • C.g‖₂ ≤ C.r := by
  refine exists_congr fun t => and_congr_right fun _ => ?_
  have : (∑ i, (p i - (C.c i + t * C.g i)) ^ 2) = ∑ i, ((p - C.c) - t • C.g) i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [norm₂, this]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
