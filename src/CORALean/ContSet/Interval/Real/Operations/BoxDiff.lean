module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.List.MinMax

@[expose] public section

/-!
# An inner approximation of the difference of two boxes

[1, Prop. 3]: of `I₁ = [l₁, u₁]` and `I₂ = [l₂, u₂]`, keep the slab of `I₁` along the axis `i*`
where `I₂` leaves the widest margin, `dₗ(i) = l₂(i) - l₁(i)` below or `dᵤ(i) = u₁(i) - u₂(i)`
above, (12): `Î = [l₁(i*), l₂(i*)[` if `dₗ(i*) ≥ dᵤ(i*)`, else `]u₂(i*), u₁(i*)]`. The slab is
half-open, so it is a set here and not a box; [1, Alg. 1] stores it closed, `boxDiffBounds`.
`argmax` keeps the first of equal margins; with no axis at all the slab is empty.

## Inputs
* `l₁` – lower bound of the first box
* `u₁` – upper bound of the first box
* `l₂` – lower bound of the second box
* `u₂` – upper bound of the second box

## Output
* inner approximation of the difference of the two boxes

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3], (11)-(12): `I₃ = {x ∈ I₁ | x(i*) ∈ Î}`. -/
noncomputable def boxDiff (l₁ u₁ l₂ u₂ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  let dl := l₂ - l₁
  let du := u₁ - u₂
  let iStar := (List.finRange n).argmax fun i => max (dl i) (du i)
  {x | x ∈ Icc l₁ u₁ ∧ ∃ i ∈ iStar,
    (du i ≤ dl i ∧ x i ∈ Ico (l₁ i) (l₂ i)) ∨ (dl i < du i ∧ x i ∈ Ioc (u₂ i) (u₁ i))}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
