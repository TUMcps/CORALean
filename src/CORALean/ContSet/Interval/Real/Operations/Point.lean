import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.point`

Zero width, which is the singleton. Composed with `plus` this is a translation,
so the representation needs no separate one — which is why a bias, a jump reset
and a linearisation offset all reach it through here.

The membership fact is one line and about this construction alone, so it stays
beside it rather than taking a file in `Theorems/`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]

def Interval.point (v : α) : Interval α := ⟨v, v⟩

-- both bounds are the point itself, so each coordinate is bounded by equality
theorem Interval.mem_point (v : α) : v ∈ (Interval.point v).construct :=
  fun _ => ⟨le_rfl, le_rfl⟩

end CORALean.Real
