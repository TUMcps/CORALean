module

public import CORALean.Global.Interfaces

@[expose] public section

/-!
# One chunk of CORA's `nnGroupSortLayer`

`reshape(input_, [groupSize numGroups_ bSz])` puts the entries `k·g, …, k·g + g - 1` of the input
in one column; the last column is padded with `Inf` up to `g` entries and the padding is cut again
after the sort. Here the chunk is taken without padding: its entries as a list, at most `g`.

## Inputs
* `g` – group size
* `x` – input vector
* `k` – group index

## Output
* the group's entries
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `k`-th chunk of `g` consecutive entries of `x`, the last one possibly shorter. -/
def groupSortChunk (g : ℕ) (x : Vec ℝ n) (k : ℕ) : List ℝ :=
  List.ofFn fun r : Fin (min g (n - k * g)) => x ⟨k * g + r, by have := r.2; omega⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
