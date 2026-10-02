import CORALean.ContSet.ContSet.ContSet

/-!
# Two nonempty sets lie in the segments between them

`segments X Y` joins every point of `X` to every point of `Y`, so for two nonempty sets it
contains both of them: take the parameter at `1` and at `0`, with any point of the other set.
With `LinComb` that is what an enclosure of CORA's `or` rests on: `linComb_outer` says only that
the segments lie in the result, which by itself says nothing about the operands.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem union_subset_segments {X Y : Set α} (hX : X.Nonempty) (hY : Y.Nonempty) :
    X ∪ Y ⊆ segments X Y := by -- --- PROOF ---
  rintro x (hx | hx)
  · obtain ⟨y, hy⟩ := hY
    exact ⟨x, hx, y, hy, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  · obtain ⟨y, hy⟩ := hX
    exact ⟨y, hy, x, hx, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
