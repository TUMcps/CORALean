module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The slice of a box through a point

`jacobiSlice x̃ ind v` is `x̃` with coordinate `ind i` replaced by `vᵢ`: the affine map
`v ↦ x̃ + P (v - x̃ ∘ ind)`, `P` the selection matrix of `ind`. It is the slice
`u₁ ↦ (u₁, ũ₂)` on which an inner-range test of `f : ℝᵐ → ℝⁿ` reduces to a square one: the
test picks the `n` columns `ind` of the Jacobian and holds the other coordinates at the
midpoint.

## Inputs
* `xc` – base point
* `ind` – indices of the replaced coordinates
* `v` – new values

## Output
* the base point with the selected coordinates replaced
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `xc` with coordinate `ind i` replaced by `v i`. -/
def jacobiSlice (xc : Fin m → ℝ) (ind : Fin n → Fin m) (v : Fin n → ℝ) : Fin m → ℝ :=
  xc + (Matrix.of fun k i => if ind i = k then (1 : ℝ) else 0) *ᵥ (v - fun i => xc (ind i))

/-- A selected coordinate reads `v`. -/
theorem jacobiSlice_apply_ind (xc : Fin m → ℝ) {ind : Fin n → Fin m}
    (hind : Function.Injective ind) (v : Fin n → ℝ) (i : Fin n) :
    jacobiSlice xc ind v (ind i) = v i := by
  simp only [jacobiSlice, Pi.add_apply, mulVec, dotProduct, of_apply, Pi.sub_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (hind h)), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, one_mul]
  ring

/-- A coordinate not selected reads `xc`. -/
theorem jacobiSlice_apply_of_ne (xc : Fin m → ℝ) {ind : Fin n → Fin m} (v : Fin n → ℝ)
    {k : Fin m} (hk : ∀ i, ind i ≠ k) : jacobiSlice xc ind v k = xc k := by
  simp [jacobiSlice, mulVec, dotProduct, hk]

/-- At the selected coordinates of `xc` itself, the slice is `xc`. -/
theorem jacobiSlice_self (xc : Fin m → ℝ) (ind : Fin n → Fin m) :
    jacobiSlice xc ind (fun i => xc (ind i)) = xc := by
  simp [jacobiSlice]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
