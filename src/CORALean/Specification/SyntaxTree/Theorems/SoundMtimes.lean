module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Operations.Mtimes
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.SoundSum
public import CORALean.Specification.SyntaxTree.Theorems.Basic

@[expose] public section

/-!
# `mtimes` of sound trees is sound

Every entry of `mtimes` over sound trees is sound.

## Inputs
* `m` – rows of the first matrix
* `k` – inner dimension minus one
* `p` – columns of the second matrix
* `A` – first matrix of trees
* `C` – second matrix of trees
* `i` – row index
* `j` – column index

## Hypotheses
* `hA` – every entry of the first matrix is sound
* `hC` – every entry of the second matrix is sound

## Conclusion
* the product entry is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every entry of `mtimes` of sound trees is sound. -/
theorem SyntaxTree.isSound_mtimes {m k p : ℕ} {A : Fin m → Fin (k + 1) → SyntaxTree n}
    {C : Fin (k + 1) → Fin p → SyntaxTree n} (hA : ∀ i l, IsSound B (A i l))
    (hC : ∀ l j, IsSound B (C l j)) (i : Fin m) (j : Fin p) : IsSound B (mtimes A C i j) :=
  isSound_sum (isSound_times (hA i 0) (hC 0 j)) _ (fun u hu => by
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hu
    exact isSound_times (hA i l.succ) (hC l.succ j))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
