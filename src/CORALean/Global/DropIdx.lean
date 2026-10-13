module

public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Every index but one

`dropIdx r` enumerates `Fin n` without `r`, in order, and `sum_dropIdx` is the
reason it exists: a sum over `Fin n` splits into the term at `r` and a sum over
everything else, with no side condition to discharge and no `Finset.erase` to
carry along afterwards.

`Fin.succAbove` already does this, but only at `Fin (n + 1)`, and a count read
off a structure field never has that shape. The two `Fin.cast`s here are that
difference and nothing else: `r : Fin n` already forces `n - 1 + 1 = n`.

`insertIdx` is `dropIdx`'s converse — built from `Fin.insertNth` the same way — and
`forall_dropIdx_iff` is `sum_dropIdx`'s counterpart for a property rather than a sum:
what a construction needs to extend a value known everywhere but `r` back to one
known everywhere.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

/-- `dropIdx`'s converse: one index of `Fin n`, built back from a value at `r` and a
value at every other index. -/
def insertIdx {n : ℕ} (r : Fin n) {M : Sort*} (a : M) (f : Fin (n - 1) → M) : Fin n → M :=
  fun l => Fin.insertNth (α := fun _ => M) (Fin.cast (Nat.succ_pred_eq_of_pos r.pos).symm r) a f
    (Fin.cast (Nat.succ_pred_eq_of_pos r.pos).symm l)

@[simp] theorem insertIdx_self {n : ℕ} (r : Fin n) {M : Sort*} (a : M) (f : Fin (n - 1) → M) :
    insertIdx r a f r = a :=
  Fin.insertNth_apply_same (α := fun _ => M) _ a f

@[simp] theorem insertIdx_dropIdx {n : ℕ} (r : Fin n) {M : Sort*} (a : M) (f : Fin (n - 1) → M)
    (i : Fin (n - 1)) : insertIdx r a f (dropIdx r i) = f i := by
  simp [insertIdx, dropIdx]

/-- A property holding everywhere splits the same way a sum does. -/
theorem forall_dropIdx_iff {n : ℕ} (r : Fin n) {P : Fin n → Prop} :
    (∀ l, P l) ↔ P r ∧ ∀ i, P (dropIdx r i) := by -- --- PROOF ---
  have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos r.pos
  refine ⟨fun hP => ⟨hP r, fun i => hP (dropIdx r i)⟩, fun ⟨hr, hi⟩ l => ?_⟩
  rcases Fin.eq_self_or_eq_succAbove (Fin.cast h.symm r) (Fin.cast h.symm l) with heq | ⟨k, heq⟩
  · have hlr : l = r := by simpa using congrArg (Fin.cast h) heq
    exact hlr ▸ hr
  · have hlk : l = dropIdx r k := by simpa [dropIdx] using congrArg (Fin.cast h) heq
    exact hlk ▸ hi k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
