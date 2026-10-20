module

public import CORALean.Global.Tensor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# `R₁(Π) = maxᵢ ‖vᵢ‖₁` fails

`[1, Eq. 30]` opens with `R₁(Π) = maxᵢ ‖vᵢ‖₁`, the rows `vᵢ = ±zᵢ` of `Π`'s
halfspace representation. For `zᵢ = eᵢ` in `ℝ²`, `Π = {|x₁| ≤ 1, |x₂| ≤ 1}`: every row has
`‖vᵢ‖₁ = 1`, but the corner `(1, 1)` of `Π` has `‖·‖₁ = 2`. The rows are vertices of `Π^Δ`,
not of `Π`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* rows of unit 1-norm exist whose polytope has a corner of 1-norm two

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem l1_norm_le_card_mul_norm_counterexample : -- --- CONCL ---
    ∃ V : Fin 4 → Vec ℝ 2, (∀ i, ∑ j, |V i j| = 1) ∧
      ∃ x : Vec ℝ 2, (∀ i, ∑ j, V i j * x j ≤ 1) ∧ ∑ j, |x j| = 2 := by -- --- PROOF ---
  refine ⟨![![1, 0], ![0, 1], ![-1, 0], ![0, -1]], fun i => ?_, ![1, 1], fun i => ?_, ?_⟩
  -- each row `±eᵢ` has `1`-norm `1`
  · fin_cases i <;> norm_num [Fin.sum_univ_two]
  -- `(1, 1)` meets every row
  · fin_cases i <;> norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
