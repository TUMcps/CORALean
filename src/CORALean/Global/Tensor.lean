import CORALean.Global.Mathlib

/-!
# Arrays: vectors, matrices, tensors

`Tensor α s` is an array of `α` of shape `s`, curried, so an entry is read by
applying one index per axis. `Vec` is its order-one case outright.

The scalar is explicit because it separates the two arithmetic layers: `Vec ℝ n`
is a point, `Vec 𝕋 n` its machine representation.

`Mat` is the order-two case up to `rfl`, but spelt as Mathlib's `Matrix`: that
wrapper keeps `*` matrix multiplication rather than the pointwise product every
function type carries, and instance search sees through it in neither direction.
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
