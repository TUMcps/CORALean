module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# The robust range of a vector-valued function

[1, Sec. II-A.2]: the values `f : ℝᵐ → ℝⁿ` reaches for every disturbance in `x_A` with some
control in `x_E`, `I_A ⊆ {1, …, m}` the disturbance inputs and `I_E` the others. Here the
inputs are one vector `x` of the box `[lo, hi]`, `IA` says which of its coordinates are the
disturbances, and `x` realizes `z` against `w` when it agrees with `w` on `IA`.

## Inputs
* `f` – vector-valued function of the inputs
* `IA` – disturbance coordinates
* `lo` – lower corner of the input box
* `hi` – upper corner of the input box

## Output
* the values reached for every disturbance with some control

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to Reachability of
      Non-Linear Control Systems With Disturbances". IEEE Control Systems Letters, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. II-A.2]: `{z | ∀ w ∈ x_A, ∃ u ∈ x_E, z = f(w, u)}` with the inputs one vector of
the box `[lo, hi]` and the disturbances the coordinates in `IA`. -/
def robustRangeVec (f : (Fin m → ℝ) → Fin n → ℝ) (IA : Finset (Fin m)) (lo hi : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {z | ∀ w ∈ Icc lo hi, ∃ x ∈ Icc lo hi, (∀ j ∈ IA, x j = w j) ∧ f x = z}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
