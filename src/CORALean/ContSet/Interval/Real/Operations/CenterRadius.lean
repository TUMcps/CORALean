import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.center` and `Interval.radius`

The midpoint and half the width: CORA's `center` and `rad`, the pair a box is
read as when an enclosure proof splits a point into a centre plus a bounded
deviation.

The two are one line each and the bound relating them names both, so they share
a file rather than each taking one of their own.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

noncomputable def Interval.center (I : Interval α) : α := (2:ℝ)⁻¹ • (I.inf + I.sup)

noncomputable def Interval.radius (I : Interval α) : α := (2:ℝ)⁻¹ • (I.sup - I.inf)

/-- A point the box denotes is the centre off by at most the radius, which is
how every enclosure proof splits it. -/
theorem Interval.abs_sub_center_le {I : Interval α} {x : α} (hx : x ∈ I.construct) (i : ι) :
    |entry x i - entry I.center i| ≤ entry I.radius i := by
  have h := hx i
  rw [Interval.center, Interval.radius, entry_smul, entry_smul, entry_add, entry_sub, abs_le]
  constructor <;> linarith [h.1, h.2]

end CORALean.Real
