module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-!
# The box difference as [1, Alg. 1] stores it

[1, Alg. 1, line 6]: `[α̲, ᾱ] = [α̲, ᾱ] \ I`, with the difference [1, Prop. 3]'s and the result
held as bounds `α̲, ᾱ ∈ ℝᵖ`: the axis `i*` and the side as `boxDiff` picks them, and the bound
on that side moved onto `I`'s, `ᾱ(i*) = l₂(i*)` or `α̲(i*) = u₂(i*)`. That is the closure of
`boxDiff`'s half-open slab, so it shares the face `α(i*) = l₂(i*)` (or `u₂(i*)`) with `I`.
[1]'s Example 5 stores its bounds so. With no axis the box is kept.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1, line 6]: the bounds of `[l₁, u₁] \ [l₂, u₂]` by [1, Prop. 3], closed. -/
noncomputable def boxDiffBounds (l₁ u₁ l₂ u₂ : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  let dl := l₂ - l₁
  let du := u₁ - u₂
  let iStar := (List.finRange n).argmax fun i => max (dl i) (du i)
  match iStar with
  | none => (l₁, u₁)
  | some i => if du i ≤ dl i then (l₁, Function.update u₁ i (l₂ i))
      else (Function.update l₁ i (u₂ i), u₁)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
