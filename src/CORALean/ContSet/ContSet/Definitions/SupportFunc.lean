module

public import Mathlib.Data.EReal.Basic

@[expose] public section

/-!
# `supportFunc`

The support function of a set, `ρ(S, ℓ) = sup_{s ∈ S} ℓ s` [1, Table 3], valued in the extended
reals so that the two conventions of [1, Eq. 33] are the definition rather than cases: `-∞` at
the empty set, `+∞` where `S` is unbounded in direction `ℓ`. A `SupportBound` is a real number
above this; nothing computes it.

## Inputs
* `S` – set
* `ℓ` – linear functional

## Output
* supremum of `ℓ` over `S` in the extended reals

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sup_{s ∈ S} ℓ s` in `[-∞, +∞]`. -/
noncomputable def supportFunc (S : Set α) (ℓ : α →ₗ[ℝ] ℝ) : EReal := ⨆ x ∈ S, (ℓ x : EReal)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
