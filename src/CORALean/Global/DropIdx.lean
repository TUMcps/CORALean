import CORALean.Global.Mathlib

/-!
# Every index but one

`dropIdx r` enumerates `Fin n` without `r`, in order, and `sum_dropIdx` is the
reason it exists: a sum over `Fin n` splits into the term at `r` and a sum over
everything else, with no side condition to discharge and no `Finset.erase` to
carry along afterwards.

`Fin.succAbove` already does this, but only at `Fin (n + 1)`, and a count read
off a structure field never has that shape. The two `Fin.cast`s here are that
difference and nothing else: `r : Fin n` already forces `n - 1 + 1 = n`.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The indices of `Fin n` other than `r`, in order. -/
def dropIdx {n : ℕ} (r : Fin n) (i : Fin (n - 1)) : Fin n :=
  Fin.cast (Nat.succ_pred_eq_of_pos r.pos)
    ((Fin.cast (Nat.succ_pred_eq_of_pos r.pos).symm r).succAbove i)

/-- A sum splits into the term at `r` and a sum over the rest. -/
theorem sum_dropIdx {M : Type*} [AddCommMonoid M] {n : ℕ} (r : Fin n) (f : Fin n → M) :
    ∑ j, f j = f r + ∑ i, f (dropIdx r i) := by
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos r.pos
  rw [← Equiv.sum_comp (finCongr h) f,
    Fin.sum_univ_succAbove (fun j => f (finCongr h j)) (Fin.cast h.symm r)]
  simp [dropIdx]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
