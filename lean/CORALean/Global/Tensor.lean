import CORALean.Global.Mathlib

/-!
# Arrays: vectors, matrices, tensors

`Tensor α s` is an array of `α` of shape `s`, curried, so an entry is read by
applying one index per axis. `Vec` is its order-one case outright.

The scalar is explicit because it is what separates the two arithmetic layers:
`Vec ℝ n` is a point, `Vec F n` its machine representation. Every signature
therefore says which arithmetic it is written in.

`Mat` is the order-two case up to `rfl`, but is spelt as Mathlib's `Matrix`:
that wrapper is what keeps `*` matrix multiplication rather than the pointwise
product every function type carries, and instance search will not see through it
in either direction. Everything else about `Mat` is `Tensor α [n, m]`.

Higher orders carry no such structure and appear as coefficient stores, e.g. the
third-order term of a Taylor remainder.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

universe u

abbrev Tensor (α : Type u) : List ℕ → Type u
  | [] => α
  | n :: s => Fin n → Tensor α s

abbrev Vec (α : Type u) (n : ℕ) := Tensor α [n]
abbrev Mat (α : Type u) (n m : ℕ) := Matrix (Fin n) (Fin m) α

theorem mat_eq_tensor (α : Type u) (n m : ℕ) : Mat α n m = Tensor α [n, m] := rfl

end CORALean
