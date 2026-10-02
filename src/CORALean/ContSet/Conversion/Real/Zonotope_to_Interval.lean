import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A zonotope as a box

CORA's `interval(zonotope)`: the centre give or take the generators' total reach
in each coordinate. Not exact — a zonotope is generally not a box — but tight,
since each coordinate's extreme is attained by taking every generator at its own
sign.

Over any ambient type with coordinates, not just `Vec ℝ n`: at `Mat ℝ m n` this
is CORA's `intervalMatrix(matZonotope)`, which is how a matrix zonotope reaches
a remainder bound, and the definition is the same one read through `Entrywise`.

No linear program: a zonotope answers a direction by summing absolute values,
which is the reason it is the representation reachability runs on.

`interval_contains` is [1, Prop. 1], which in turn cites Althoff 2010, Prop. 2.2 — not
formalized separately, since nothing here draws on the thesis beyond this same formula.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   12-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

def Zonotope.interval (Z : Zonotope α) : Interval α where
  inf := ofEntry fun i => entry Z.c i - ∑ j, |entry (Z.G j) i|
  sup := ofEntry fun i => entry Z.c i + ∑ j, |entry (Z.G j) i|


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1]: the box built from a zonotope's centre and generator widths
contains it. -/
theorem Zonotope.interval_contains (Z : Zonotope α) :
    Z.construct ⊆ Z.interval.construct := by -- --- PROOF ---
  rintro x ⟨β, hβ, rfl⟩
  intro i
  have key : |∑ j, entry (Z.G j) i * β j| ≤ ∑ j, |entry (Z.G j) i| :=
    calc |∑ j, entry (Z.G j) i * β j|
        ≤ ∑ j, |entry (Z.G j) i * β j|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |entry (Z.G j) i| * |β j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |entry (Z.G j) i|         := by
          refine Finset.sum_le_sum fun j _ => ?_
          simpa using mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg (entry (Z.G j) i))
  rw [abs_le] at key
  -- both faces, the same magnitude bound signed either way
  simp only [Zonotope.interval, entry_ofEntry, entry_add_sum_smul]
  constructor <;> linarith [key.1, key.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
