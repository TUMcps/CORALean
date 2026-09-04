import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Interval.Real.Interval

/-!
# A zonotope as a box

CORA's `interval(zonotope)`: the centre give or take the generators' total reach
in each coordinate. Not exact — a zonotope is generally not a box — but tight,
since each coordinate's extreme is attained by taking every generator at its own
sign.

No linear program: a zonotope answers a direction by summing absolute values,
which is the reason it is the representation reachability runs on.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Zonotope.interval (Z : Zonotope (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun i => Z.c i - ∑ j, |Z.G j i|
  sup := fun i => Z.c i + ∑ j, |Z.G j i|

theorem Zonotope.interval_outer (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.interval.construct := by
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  intro i
  have key : |x i - Z.c i| ≤ ∑ j, |Z.G j i| := by
    rw [hx i, add_sub_cancel_left]
    calc |∑ j, Z.G j i * β j|
        ≤ ∑ j, |Z.G j i * β j|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |Z.G j i| * |β j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |Z.G j i|         := by
          refine Finset.sum_le_sum fun j _ => ?_
          simpa using mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg (Z.G j i))
  rw [abs_le] at key
  -- both faces, the same magnitude bound signed either way
  constructor
  · show Z.c i - ∑ j, |Z.G j i| ≤ x i
    linarith [key.1]
  · show x i ≤ Z.c i + ∑ j, |Z.G j i|
    linarith [key.2]

end CORALean.Real
