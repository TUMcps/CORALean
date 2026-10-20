module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Membership in an interval matrix, by row and column

`construct` indexes an ambient type by whatever `Entrywise` says its coordinates
are, which for `Mat ℝ m n` is a pair. Every enclosure over a matrix states its
bounds with two indices instead, and this is the reading that gets it there.

CORA's `intervalMatrix` is `Interval (Mat ℝ m n)`, so this is the only place the
pair index has to be taken apart.

## Inputs
* `m` – number of rows
* `n` – number of columns
* `I` – interval matrix
* `A` – real matrix

## Hypotheses
* none

## Conclusion
* membership holds iff every entry lies between its bounds
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

-- the pair index split one way and reassembled the other
theorem Interval.mem_mat_iff {m n : ℕ} {I : Interval (Mat ℝ m n)} {A : Mat ℝ m n} :
    A ∈ I.construct ↔ ∀ i j, I.inf i j ≤ A i j ∧ A i j ≤ I.sup i j :=
  ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
