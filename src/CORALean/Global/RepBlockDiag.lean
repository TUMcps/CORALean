module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Repeated blocks

`a` copies of a vector side by side (`repVec`) and `a` copies of a matrix on the diagonal of a
block matrix (`repBlockDiag`), an entry outside the blocks being the zero given explicitly, so that
a float scalar, which has no `Zero` instance, can use it too, as for `blockDiag`. The rows and
columns are both split by `finProdFinEquiv`, so the block an index belongs to and its position
inside it are read off the same equivalence. It is the shape of a system repeated on fresh
variables (`PolyLevelSet.copies`), and of every matrix of the convex hull of a constrained
polynomial zonotope. The lemmas read a sum or a product over the blocks as one over each block, and
a column of `repBlockDiag` as block `j`'s alone.

## Inputs
* `β` – entry type
* `z` – zero entry
* `a` – number of copies
* `r` – rows of a block
* `c` – columns of a block
* `M` – block to be repeated

## Output
* the block matrix with one copy of the block per diagonal position
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       13-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

/-- `a` copies of `v`, an index reading the entry at its position in its block. -/
def repVec {β : Type} (a : ℕ) {r : ℕ} (v : Fin r → β) : Fin (a * r) → β :=
  fun x => v (finProdFinEquiv.symm x).2


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One copy of `M` per block on the diagonal, and `z` off the blocks. -/
def repBlockDiag {β : Type} (z : β) (a : ℕ) {r c : ℕ} (M : Fin r → Fin c → β) :
    Fin (a * r) → Fin (a * c) → β := fun x y =>
  if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm y).1
  then M (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2 else z

/-- A sum over `a` blocks of `r`, as a sum of sums. -/
theorem sum_rep {M : Type} [AddCommMonoid M] {a r : ℕ} (F : Fin (a * r) → M) :
    ∑ x, F x = ∑ j : Fin a, ∑ k : Fin r, F (finProdFinEquiv (j, k)) := by
  rw [← Equiv.sum_comp finProdFinEquiv F, Fintype.sum_prod_type]

/-- A product over `a` blocks of `r`, as a product of products. -/
theorem prod_rep {M : Type} [CommMonoid M] {a r : ℕ} (F : Fin (a * r) → M) :
    ∏ x, F x = ∏ j : Fin a, ∏ k : Fin r, F (finProdFinEquiv (j, k)) := by
  rw [← Equiv.prod_comp finProdFinEquiv F, Fintype.prod_prod_type]

/-- Block `j`'s column of `repBlockDiag 0 a E` names `E`'s column over block `j`'s own
variables. -/
theorem prod_repBlockDiag {a p h : ℕ} (E : Fin p → Fin h → ℕ) (v : Fin (a * p) → ℝ)
    (j : Fin a) (i : Fin h) :
    (∏ x, v x ^ repBlockDiag 0 a E x (finProdFinEquiv (j, i)))
      = ∏ k, v (finProdFinEquiv (j, k)) ^ E k i := by -- --- PROOF ---
  rw [prod_rep (fun x => v x ^ repBlockDiag 0 a E x (finProdFinEquiv (j, i)))]
  refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  -- off the diagonal the whole block sits at exponent zero
  · exact Finset.prod_eq_one fun k _ => by simp [repBlockDiag, hj']
  · exact Finset.prod_congr rfl fun k _ => by simp [repBlockDiag]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
