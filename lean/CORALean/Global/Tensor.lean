import CORALean.Global.Mathlib

/-!
# Real arrays: vectors, matrices, tensors

`Tensor s` is an array of reals of shape `s`, curried, so an entry is read by
applying one index per axis. `Vec` is its order-one case outright.

`Mat` is the order-two case up to `rfl`, but is spelt as Mathlib's `Matrix`:
that wrapper is what keeps `*` matrix multiplication rather than the pointwise
product every function type carries, and instance search will not see through it
in either direction. Everything else about `Mat` is `Tensor [n, m]`.

Higher orders carry no such structure and appear as coefficient stores, e.g. the
third-order term of a Taylor remainder.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

abbrev Tensor : List ℕ → Type
  | [] => ℝ
  | n :: s => Fin n → Tensor s

abbrev Vec (n : ℕ) := Tensor [n]
abbrev Mat (n m : ℕ) := Matrix (Fin n) (Fin m) ℝ

theorem mat_eq_tensor (n m : ℕ) : Mat n m = Tensor [n, m] := rfl

end CORALean
