import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.and`

Intersecting two boxes, coordinatewise and exactly: a point is in both when each
of its coordinates clears both lower bounds and stays under both upper ones.

The result may be empty, and says so the way this representation always does —
some coordinate's `sup` below its `inf`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

def Interval.and (I₁ I₂ : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun j => max (I₁.inf j) (I₂.inf j)
  sup := fun j => min (I₁.sup j) (I₂.sup j)

theorem Interval.and_exact (I₁ I₂ : Interval (Vec ℝ n)) :
    (I₁.and I₂).construct = I₁.construct ∩ I₂.construct := by
  ext x
  constructor
  · intro h
    refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
    · exact (max_le_iff.mp (h j).1).1
    · exact (le_min_iff.mp (h j).2).1
    · exact (max_le_iff.mp (h j).1).2
    · exact (le_min_iff.mp (h j).2).2
  · rintro ⟨h₁, h₂⟩ j
    exact ⟨max_le (h₁ j).1 (h₂ j).1, le_min (h₁ j).2 (h₂ j).2⟩

end CORALean.Real
