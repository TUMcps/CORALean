module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `[1, Eq. 29]` fails

In `ℝ¹`, `z₁ = 2`: `∑ [-1, 1] z₁ = [-2, 2]`, while `{x | V x ≤ 1}` with `V = (2, -2)ᵀ` is
`[-1/2, 1/2]`; the point `2` is in the first and not the second.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the parallelotope is not the claimed halfspace set

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.parallelotope_eq_abs_mulVec_le_counterexample : -- --- CONCL ---
    (⟨1, 0, fun _ => ![2]⟩ : Zonotope (Vec ℝ 1)).construct
      ≠ {x | ∀ i, ((!![2; -2] : Mat ℝ 2 1) *ᵥ x) i ≤ 1} := by -- --- PROOF ---
  intro heq
  -- `2 = 0 + 1 · 2` is in the zonotope
  have hmem : (![2] : Vec ℝ 1) ∈ (⟨1, 0, fun _ => ![2]⟩ : Zonotope (Vec ℝ 1)).construct :=
    ⟨fun _ => 1, fun _ => by simp, by ext i; fin_cases i; simp⟩
  rw [heq] at hmem
  have := hmem 0
  norm_num [mulVec, dotProduct] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
