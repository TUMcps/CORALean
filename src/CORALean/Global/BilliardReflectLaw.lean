module

public import CORALean.Global.BilliardReflect

@[expose] public section

/-!
# The reflection law of the billiard

`[1, Alg., step 3]` calls it "the angle of incidence equals the angle of reflection", and
`[1, Thm. 1]` reads its symmetry off it. With `‖s‖ = 1` the reflected direction has the
opposite component along the normal, the same component along the wall, and the same length:
speed stays constant, as the introduction says of the gas particle.

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

theorem billiardReflect_law (s d : E) (hs : ‖s‖ = 1) :
    inner ℝ (billiardReflect s d) s = -inner ℝ d s ∧
      billiardReflect s d - inner ℝ (billiardReflect s d) s • s = d - inner ℝ d s • s ∧
      ‖billiardReflect s d‖ = ‖d‖ := by -- --- PROOF ---
  -- `(s, s) = 1`
  have hss : inner ℝ s s = 1 := by rw [real_inner_self_eq_norm_sq, hs]; norm_num
  -- the normal component flips
  have h1 : inner ℝ (billiardReflect s d) s = -inner ℝ d s := by
    simp only [billiardReflect, inner_sub_left, inner_smul_left, hss]
    simp; ring
  refine ⟨h1, ?_, ?_⟩
  · -- the wall component is untouched
    rw [h1]; simp only [billiardReflect]
    module
  · -- the length is unchanged: compare squares
    have hsq : ‖billiardReflect s d‖ ^ 2 = ‖d‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      simp only [billiardReflect, inner_sub_left, inner_sub_right, inner_smul_left,
        inner_smul_right, hss, real_inner_comm d s]
      simp; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
