module

public import CORALean.ContSet.ContSet.Operations.Decompose
public import CORALean.ContSet.ContSet.Theorems.ProjectOuter

@[expose] public section

/-!
# `ContSet.decompose` encloses every block's projection

Block `i` contains the run of coordinates `lo i, …, lo i + len i - 1` of every point of the set.
Outer, since each block is a `project`; the blocks together enclose the set's projection onto
each run, not the set (the product of the blocks is wider in general).
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.decompose_outer (s : S n) (lo len : Fin b → ℕ) (h : ∀ i, lo i + len i ≤ n)
    (i : Fin b) :
    (fun x : Vec ℝ n =>
        (fun j : Fin (len i) => x ⟨lo i + j, by have := h i; omega⟩ : Vec ℝ (len i))) ''
        construct s ⊆ construct (ContSet.decompose (𝕋 := 𝕋) s lo len h i) :=
  ContSet.project_outer (𝕋 := 𝕋) s _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
