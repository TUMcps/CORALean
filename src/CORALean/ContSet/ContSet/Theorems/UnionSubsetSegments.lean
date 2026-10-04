import CORALean.ContSet.ContSet.ContSet

/-!
# Two nonempty sets lie in the segments between them

`segments X Y` joins every point of `X` to every point of `Y`, so for two nonempty sets it
contains both of them: take the parameter at `1` and at `0`, with any point of the other set.
With `LinComb` that is what an enclosure of CORA's `or` rests on: `linComb_outer` says only that
the segments lie in the result, which by itself says nothing about the operands.

[1, Eq. 37] encloses a union by the convex hull; with the `conv` of [1, Table 3], which is
`segments`, that needs both operands nonempty, as here.

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification for Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
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
