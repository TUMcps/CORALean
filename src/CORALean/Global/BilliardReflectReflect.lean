module

public import CORALean.Global.BilliardReflect

@[expose] public section

/-!
# The billiard reflection is its own inverse

A trajectory run backwards bounces off the same wall the same way (step 3 of `[1, Alg.]`): this is
the local half of the reversibility `[1, Thm. 1]` uses ("reversibility of a billiard trajectory
due to the reflection law"), the half a theorem of reals can state without a measure on
directions. The density symmetry the proof of `[1, Thm. 1]` builds on it is not covered.

## Inputs
* `s` – wall normal
* `d` – incoming direction

## Hypotheses
* `hs` – the normal has unit length

## Conclusion
* reflecting twice returns the incoming direction

## References

* [1] B. T. Polyak and E. N. Gryazina. "Billiard walk - a new sampling algorithm for control
      and optimization". In Proc. of the 19th IFAC World Congress, Cape Town, South Africa,
      IFAC Proceedings Volumes 47(3), pp. 6123-6128, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem billiardReflect_reflect (s d : E) (hs : ‖s‖ = 1) : -- --- CONCL ---
    billiardReflect s (billiardReflect s d) = d := by -- --- PROOF ---
  have hss : inner ℝ s s = 1 := by rw [real_inner_self_eq_norm_sq, hs]; norm_num
  -- the normal component of the reflected direction is the negated one
  have h1 : inner ℝ (billiardReflect s d) s = -inner ℝ d s := by
    simp only [billiardReflect, inner_sub_left, inner_smul_left, hss]
    simp; ring
  simp only [billiardReflect] at h1 ⊢
  rw [h1]
  module

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
