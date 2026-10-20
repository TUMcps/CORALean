module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# `Zonotope.ofOneParamPoly`

A zonotope enclosing the polynomial `β ↦ Σ_{k=0}^N βᵏ v_k` over `β ∈ [-1, 1]`, by the device of
the proof of [1, Thm. 1]: an odd power ranges over `[-1, 1]`, so `v_k` is a generator; an even
power over `[0, 1]`, so `½ v_k` goes to the center and `½ v_k` is the generator. Generator `j`
belongs to the power `j + 1`; the center is `v_0 + Σ_{l=1}^{⌊N/2⌋} ½ v_{2l}`. The powers are
treated as independent, which is where the enclosure gives something away.

## Inputs
* `v` – polynomial coefficients
* `N` – polynomial degree

## Output
* zonotope enclosing the polynomial over `[-1, 1]`

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.ofOneParamPoly (v : ℕ → α) (N : ℕ) : Zonotope α where
  h := N
  c := v 0 + ∑ l ∈ Finset.Icc 1 (N / 2), (1 / 2 : ℝ) • v (2 * l)
  G := fun j => if Odd (j.val + 1) then v (j.val + 1) else (1 / 2 : ℝ) • v (j.val + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
