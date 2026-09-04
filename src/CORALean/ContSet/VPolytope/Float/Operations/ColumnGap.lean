import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.columnGap`

A box wide enough for every column's rounding at once. The operations here store
a whole vertex list, and a hull has no centre to move a vertex away from, so one
box has to cover all of it — the widest gap in each coordinate, taken over the
columns.

`mem_columnGap` is what a caller storing the lower rounding of one column then
puts into that box, and it is stated per column because that is how a vertex is
placed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def VPolytope.columnGap {k : ℕ} (lo hi : Mat 𝕋 n k) : Interval 𝕋 n :=
  ⟨fun _ => zero, fun i => maximumOver fun l => subUp (hi i l) (lo i l)⟩

/-- Storing the lower rounding of column `l` leaves a residual the gap admits. -/
theorem VPolytope.mem_columnGap [SoundFloatArithmetic 𝕋] {k : ℕ} {lo hi : Mat 𝕋 n k}
    {p : Vec ℝ n} {l : Fin k}
    (h : ∀ i, toReal (lo i l) ≤ p i ∧ p i ≤ toReal (hi i l)) :
    (fun i => p i - toReal (lo i l)) ∈ (VPolytope.columnGap lo hi).construct := by
  refine fun i => ⟨?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ p i - toReal (lo i l)
    rw [toReal_zero]
    linarith [(h i).1]
  -- the column's own gap first, then the maximum over all of them
  · show p i - toReal (lo i l) ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l'))
    calc p i - toReal (lo i l)
        ≤ toReal (hi i l) - toReal (lo i l) := by linarith [(h i).2]
      _ ≤ toReal (subUp (hi i l) (lo i l)) := sub_le_subUp _ _
      _ ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l')) :=
          le_maximumOver (fun l' => subUp (hi i l') (lo i l')) l

end CORALean.Float
