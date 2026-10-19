module

public import CORALean.ContSet.Capsule.Real.Theorems.ContainsPointIff

@[expose] public section

/-!
# [1, Table 2]'s capsule test, its first inequality made non-strict, is exact

With `δ = x - c` and `g_n = g / ‖g‖₂`, `x` lies in the capsule iff the foot of its
projection falls strictly inside the axis and the distance to the axis is at most `r`, or
one of the two end spheres contains it. [1, Table 2] prints the axis test with `< r`,
which misses the capsule's boundary (`ContainsTable`); with `≤ r` it is
CORA's `aux_containsPoint` plus the end spheres unconditionally, which add nothing since
both lie in the capsule.

## Inputs
* `C` – capsule
* `x` – point

## Hypotheses
* none

## Conclusion
* membership is the table test of [1]

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Table 2]'s capsule test, at `≤ r` on the axis, decides membership. -/
theorem Capsule.mem_iff_table (C : Capsule n) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ C.construct ↔
      (‖((x - C.c) ⬝ᵥ (‖C.g‖₂⁻¹ • C.g)) • (‖C.g‖₂⁻¹ • C.g) - (x - C.c)‖₂ ≤ C.r ∧
          |(x - C.c) ⬝ᵥ (‖C.g‖₂⁻¹ • C.g)| < ‖C.g‖₂) ∨
        ‖(x - C.c) - C.g‖₂ ≤ C.r ∨ ‖(x - C.c) + C.g‖₂ ≤ C.r := by -- --- PROOF ---
  -- the axis distance and the end distances, in `containsPoint`'s spelling
  have hax : ∀ s : ℝ, ‖(C.c + s • (‖C.g‖₂⁻¹ • C.g)) - x‖₂
      = ‖s • (‖C.g‖₂⁻¹ • C.g) - (x - C.c)‖₂ := fun s => by congr 1; abel
  have hend₁ : ‖x - (C.c + C.g)‖₂ = ‖(x - C.c) - C.g‖₂ := by congr 1; abel
  have hend₂ : ‖x - (C.c - C.g)‖₂ = ‖(x - C.c) + C.g‖₂ := by congr 1; abel
  constructor
  · intro hx
    rcases (C.containsPoint_iff x).mpr hx with ⟨hlt, hle⟩ | ⟨-, h | h⟩
    · exact Or.inl ⟨by rwa [hax] at hle, hlt⟩
    · exact Or.inr (Or.inl (by rwa [hend₁] at h))
    · exact Or.inr (Or.inr (by rwa [hend₂] at h))
  · rintro (⟨hle, hlt⟩ | h | h)
    · exact (C.containsPoint_iff x).mp (Or.inl ⟨hlt, by rwa [hax]⟩)
    · -- an end sphere lies in the capsule: `t = 1`
      exact (C.mem_construct_iff_norm₂ x).mpr ⟨1, ⟨by norm_num, le_rfl⟩, by rwa [one_smul]⟩
    · exact (C.mem_construct_iff_norm₂ x).mpr
        ⟨-1, ⟨le_rfl, by norm_num⟩, by rwa [neg_one_smul, sub_neg_eq_add]⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
