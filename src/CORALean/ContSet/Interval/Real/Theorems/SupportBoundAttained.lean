module

public import CORALean.ContSet.Interval.Real.Operations.SupportBound
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty

@[expose] public section

/-!
# A nonempty box's support bound is its support function

`Interval.step_supportBoundEntrywise` claims only that nothing exceeds the value. For
a box whose bounds do not cross the value is a maximum: coordinate `i` is moved
to whichever endpoint the sign of the direction's weight on it picks, and
`Entrywise.ofEntry` assembles that point. An empty box has a bound and no point
attaining it, so the hypothesis cannot be dropped.

## Inputs
* `n` – dimension
* `I` – interval
* `c` – linear functional

## Hypotheses
* `hI` – `I` nonempty

## Conclusion
* some point of the box attains the support bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Interval.aux_supportBoundEntrywise_attained [Fintype ι] [DecidableEq ι]
    (I : Interval α) (c : α →ₗ[ℝ] ℝ) (hI : I.IsNonempty) : -- --- CONCL ---
    ∃ x ∈ I.construct, c x = (I.step_supportBoundEntrywise c).val := by -- --- PROOF ---
  classical
  -- the weight each coordinate carries; the far endpoint is the one its sign picks
  set w : ι → ℝ := fun i => c (ofEntry (Pi.single i 1)) with hw
  let f : ι → ℝ := fun i => if w i * entry I.inf i ≤ w i * entry I.sup i
    then entry I.sup i else entry I.inf i
  refine ⟨ofEntry f, fun i => ?_, ?_⟩
  -- the point lies in the box: both choices are endpoints, and the box is nonempty
  · rw [entry_ofEntry]
    by_cases h : w i * entry I.inf i ≤ w i * entry I.sup i
    · simp only [f, if_pos h]
      exact ⟨hI i, le_rfl⟩
    · simp only [f, if_neg h]
      exact ⟨le_rfl, hI i⟩
  -- its value is the sum of the corner products, coordinate by coordinate
  · have hc : c (ofEntry f) = ∑ i, entry (ofEntry f : α) i * w i := by
      conv_lhs => rw [eq_sum_single (ofEntry f : α), map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [entry_ofEntry, mul_comm]
    by_cases h : w i * entry I.inf i ≤ w i * entry I.sup i
    · simp only [f, if_pos h]
      exact (max_eq_right h).symm
    · simp only [f, if_neg h]
      exact (max_eq_left (le_of_not_ge h)).symm


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Interval.aux_supportBoundEntrywise_attained` at the ambient type `Vec ℝ n`. -/
theorem Interval.supportBound_attained {n : ℕ} (I : Interval (Vec ℝ n))
    (c : Vec ℝ n →ₗ[ℝ] ℝ) (hI : I.IsNonempty) :
    ∃ x ∈ I.construct, c x = (I.supportBound c).val :=
  Interval.aux_supportBoundEntrywise_attained I c hI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
