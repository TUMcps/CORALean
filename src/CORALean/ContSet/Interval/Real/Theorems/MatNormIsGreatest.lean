module

public import CORALean.ContSet.Interval.Real.Operations.MatNorm
public import CORALean.ContSet.Interval.Real.Theorems.AbsCenterAddRadius
public import CORALean.ContSet.Interval.Real.Theorems.ExistsMemAbsEqAbsMax
public import CORALean.ContSet.Interval.Real.Theorems.NormTypeEvalMono

@[expose] public section

/-!
# `Interval.matNorm` is the maximum norm over the box

For the types CORA supports, `norm(|center| + rad, type)` bounds the norm of every member of the
box, and the corner of larger magnitude in every entry attains it: the norms depend on the
absolute values of the entries only and are monotone in them. The type `2` is excluded by
construction; CORA refuses it because the maximum is NP-hard.

## Inputs
* `p` – norm type
* `A` – interval matrix

## Hypotheses
* `hA` – `A` has ordered bounds

## Conclusion
* the matrix norm of the box is the greatest member norm
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The maximum of the norm of `type` over a nonempty box is `matNorm`, and is attained. -/
theorem Interval.matNorm_isGreatest (p : Interval.NormType) (A : Interval (Mat ℝ m n))
    (hA : ∀ r s, A.inf r s ≤ A.sup r s) :
    IsGreatest ((fun M : Mat ℝ m n => p.eval M) '' A.construct) (A.matNorm p) := by -- --- PROOF ---
  have hmax : A.matNorm p = p.eval A.absMax := by
    unfold Interval.matNorm
    exact congrArg p.eval (funext fun i => funext fun j => Interval.abs_center_add_radius A hA i j)
  have hnn : ∀ i j, |A.absMax i j| = A.absMax i j := fun i j =>
    abs_of_nonneg (le_max_of_le_left (abs_nonneg _))
  rw [hmax]
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hMa⟩ := Interval.exists_mem_abs_eq_absMax A hA
    refine ⟨M, hM, le_antisymm (p.eval_mono fun i j => ?_) (p.eval_mono fun i j => ?_)⟩
    · rw [hMa, hnn]
    · rw [hMa, hnn]
  · rintro _ ⟨M, hM, rfl⟩
    refine p.eval_mono fun i j => ?_
    rw [hnn]
    have h := Interval.mem_mat_iff.mp hM i j
    show |M i j| ≤ max |A.inf i j| |A.sup i j|
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (A.inf i j), le_max_left |A.inf i j| |A.sup i j|, h.1],
      h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
