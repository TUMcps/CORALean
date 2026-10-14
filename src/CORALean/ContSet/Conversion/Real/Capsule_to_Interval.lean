module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Interval.Real.Interval
public import CORALean.ContSet.Conversion.Real.Operations.Capsule_to_Interval

@[expose] public section

/-!
# A capsule as a box

CORA's `interval(capsule)`: the centre give or take the generator's reach and
the ball's radius in each coordinate. One coordinate of a point never exceeds
the whole Euclidean distance it is a part of, `aux_abs_le_sqrt_sumSq`, and `t`
ranging over `[-1, 1]` bounds `t * g i` by `|g i|`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate never exceeds the whole Euclidean distance. -/
theorem aux_abs_le_sqrt_sumSq (y : Vec ℝ n) (i : Fin n) :
    |y i| ≤ Real.sqrt (∑ j, y j ^ 2) := by
  have h : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
    Finset.single_le_sum (f := fun j => y j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  calc |y i| = Real.sqrt (y i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, y j ^ 2) := Real.sqrt_le_sqrt h


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.interval_contains (C : Capsule n) :
    C.construct ⊆ C.interval.construct := by -- --- PROOF ---
  rintro x ⟨t, ht, hle⟩ i
  simp only [Capsule.interval]
  have hbound : |x i - (C.c i + t * C.g i)| ≤ C.r :=
    le_trans (aux_abs_le_sqrt_sumSq (fun j => x j - (C.c j + t * C.g j)) i) hle
  have habs := abs_le.mp hbound
  have htabs : |t| ≤ 1 := abs_le.mpr ht
  have htg := abs_le.mp (calc |t * C.g i| = |t| * |C.g i| := abs_mul t (C.g i)
    _ ≤ 1 * |C.g i| := mul_le_mul_of_nonneg_right htabs (abs_nonneg _)
    _ = |C.g i| := one_mul _)
  constructor
  · show C.c i - (|C.g i| + C.r) ≤ x i
    linarith [habs.1, htg.1]
  · show x i ≤ C.c i + (|C.g i| + C.r)
    linarith [habs.2, htg.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
