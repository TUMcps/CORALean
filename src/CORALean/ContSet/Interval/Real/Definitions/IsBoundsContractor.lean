module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# What a contractor owes

[1, Def. 3]: `contract(I) ⊆ I` and every `x ∈ I` with `c(x) = 0` stays in `contract(I)`. A box is
held by its bounds, and [1]'s boxes `[l, u]` have `l ≤ u` by its notation, so the inclusion is of
bounds, `l ≤ l' ≤ u' ≤ u`, at every `l ≤ u`: a contractor cannot answer with an empty box, which
is what lets [1, Alg. 1] subtract its answer with [1, Prop. 3]. `IsContractor` is the same
definition at a scalar constraint and set inclusion, where an empty answer may carry any bounds;
here the constraint is vector-valued, as [1, Prop. 2] produces it.

## Inputs
* `m` – dimension
* `F` – codomain type with zero
* `c` – function whose zeros are kept
* `contract` – box contractor

## Output
* every box shrinks and keeps all zeros of `c`

## References

* [1] N. Kochdumper and M. Althoff. "Computing Non-Convex Inner-Approximations of Reachable Sets
      for Nonlinear Continuous Systems". In Proc. of the 59th IEEE Conference on Decision and
      Control (CDC), pp. 2130-2137, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Set


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Def. 3]: `contract` shrinks every box `[l, u]` and keeps every zero of `c` in it. -/
def IsBoundsContractor {m : ℕ} {F : Type} [Zero F] (c : (Fin m → ℝ) → F)
    (contract : (Fin m → ℝ) × (Fin m → ℝ) → (Fin m → ℝ) × (Fin m → ℝ)) : Prop :=
  ∀ l u : Fin m → ℝ, l ≤ u →
    (l ≤ (contract (l, u)).1 ∧ (contract (l, u)).1 ≤ (contract (l, u)).2 ∧
      (contract (l, u)).2 ≤ u) ∧
    ∀ x ∈ Icc l u, c x = 0 → x ∈ Icc (contract (l, u)).1 (contract (l, u)).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
