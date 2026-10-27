module

public import Mathlib.Analysis.Convex.Segment
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A segment meets a vertical line iff the line is between its ends

`[P; Q] ∩ {z | z₀ = γ}` is nonempty exactly when `γ` lies between `P₀` and `Q₀`. It is the test of
lines 18, 11 and 19 of [1, Alg. 3] and [1, Alg. 4] ("`[P; P + s₁]` intersects `L_γ`") read as an
inequality on the abscissae, which is how the bisection of `Alg. 4` is followed.

## Inputs
* `P` – segment start
* `Q` – segment end
* `γ` – abscissa of the vertical line

## Hypotheses
* none

## Conclusion
* the segment meets the line iff `γ` lies between the endpoint abscissae

## References

* [1] [A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". Hybrid Systems: Computation and Control,
      2008.](../../../../../../references/2008/girard-hscc-zonotope-hyperplane.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.segment_meets_vline_iff (P Q : Vec ℝ 2) (γ : ℝ) : -- --- CONCL ---
    (segment ℝ P Q ∩ {z | z 0 = γ}).Nonempty ↔
      min (P 0) (Q 0) ≤ γ ∧ γ ≤ max (P 0) (Q 0) := by -- --- PROOF ---
  -- `P + t (Q - P)` for `t ∈ [0, 1]`
  rw [segment_eq_image']
  constructor
  · rintro ⟨z, ⟨t, ⟨ht0, ht1⟩, rfl⟩, hz⟩
    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hz
    rcases le_total (P 0) (Q 0) with h | h
    · rw [min_eq_left h, max_eq_right h]
      constructor <;> nlinarith
    · rw [min_eq_right h, max_eq_left h]
      constructor <;> nlinarith
  -- conversely, the point of the segment at the abscissa `γ`
  · rintro ⟨h1, h2⟩
    by_cases hPQ : P 0 = Q 0
    · refine ⟨P, ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩, ?_⟩
      rw [hPQ] at h1 h2
      simp only [Set.mem_setOf_eq]
      rw [min_self] at h1
      rw [max_self] at h2
      rw [hPQ]
      linarith
    -- a nonvertical segment: the parameter is `(γ - P₀) / (Q₀ - P₀)`
    · have hne : Q 0 - P 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
      refine ⟨P + ((γ - P 0) / (Q 0 - P 0)) • (Q - P), ⟨_, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · rcases le_total (P 0) (Q 0) with h | h
        · rw [min_eq_left h] at h1
          exact div_nonneg (by linarith) (by linarith)
        · rw [max_eq_left h] at h2
          exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · rcases le_total (P 0) (Q 0) with h | h
        · rw [max_eq_right h] at h2
          exact (div_le_one (by linarith [lt_of_le_of_ne h hPQ])).mpr (by linarith)
        · rw [min_eq_right h] at h1
          have : Q 0 < P 0 := lt_of_le_of_ne h (Ne.symm hPQ)
          exact (div_le_one_of_neg (by linarith)).mpr (by linarith)
      · simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
