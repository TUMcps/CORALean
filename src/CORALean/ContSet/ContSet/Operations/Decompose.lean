module

public import CORALean.ContSet.ContSet.Operations.Project

@[expose] public section

/-!
# CORA's `decompose`: a set cut into blocks of coordinates

`S_out{i} = project(S, blocks(i,1):blocks(i,2))`: one set per block, each the projection onto a
run of consecutive coordinates. A block is its first coordinate `lo i` (zero-based) and its
length `len i`, the run `lo i, …, lo i + len i - 1`, which must lie inside `n`. CORA's `blocks`
are the one-based inclusive pairs of the same runs, and its one-block shortcut `S.copy()` is
the identity projection, which this gives too.

## Inputs
* `s` – set
* `lo` – first coordinate of each block
* `len` – length of each block

## Hypotheses
* `h` – every block fits within the dimension

## Output
* the family of block projections of `s`
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n b : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `decompose(S, blocks)`: block `i` is the projection onto the coordinates
`lo i, …, lo i + len i - 1`. -/
def ContSet.decompose (s : S n) (lo len : Fin b → ℕ) (h : ∀ i, lo i + len i ≤ n) :
    (i : Fin b) → S (len i) :=
  fun i => ContSet.project (𝕋 := 𝕋) s (fun j : Fin (len i) => ⟨lo i + j, by have := h i; omega⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
