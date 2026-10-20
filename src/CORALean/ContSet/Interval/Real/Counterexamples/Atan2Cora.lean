module

public import CORALean.ContSet.Interval.Real.Operations.Atan2

@[expose] public section

/-!
# CORA's `interval/atan2` is not an enclosure across the branch cut

`@interval/atan2.m` returns the hull of `atan2` at the four corners only. For `y ∈ [-1, 1]` and
`x = [-1, -1]` the corners give `[-3π/4, 3π/4]`, but `atan2(0, -1) = π`, which is not in it:
`atan2` is not monotone on a box that crosses the negative real axis, and its extremum `π` is
attained in the interior of the `y` range. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* boxes and points where CORA's arctangent result misses the true value
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Points `y ∈ [-1, 1]`, `x = -1` whose `atan2` is not in CORA's corner hull. -/
theorem Interval.atan2_cora_counterexample :
    ∃ (I₁ I₂ : Interval (Vec ℝ 1)) (y x : Vec ℝ 1), y ∈ I₁.construct ∧ x ∈ I₂.construct ∧
      (fun i => Complex.arg ⟨x i, y i⟩) ∉ (I₁.atan2 I₂).construct := by -- --- PROOF ---
  refine ⟨⟨fun _ => -1, fun _ => 1⟩, ⟨fun _ => -1, fun _ => -1⟩, fun _ => 0, fun _ => -1,
    fun i => ⟨by show (-1 : ℝ) ≤ 0; norm_num, by show (0 : ℝ) ≤ 1; norm_num⟩,
    fun i => ⟨le_rfl, le_rfl⟩, fun h => ?_⟩
  have h0 := (h 0).2
  have hpi : Complex.arg ⟨-1, 0⟩ = Real.pi := by
    rw [Complex.arg_eq_pi_iff]; exact ⟨by norm_num, rfl⟩
  have h1 : Complex.arg ⟨-1, -1⟩ < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) fun e => by
      rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 (by norm_num)
  have h2 : Complex.arg ⟨-1, 1⟩ < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) fun e => by
      rw [Complex.arg_eq_pi_iff] at e; exact absurd e.2 (by norm_num)
  simp only [Interval.atan2, hpi] at h0
  simp at h0
  have h3 : Real.pi ≤ max (Complex.arg ⟨-1, -1⟩) (Complex.arg ⟨-1, 1⟩) := h0
  exact absurd h3 (not_le.mpr (max_lt h1 h2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
