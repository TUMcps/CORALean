module

public import CORALean.ContSet.ConZonotope.Real.Theorems.MemOfMatIff
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# A linear program with a minimum-norm solution

The step behind [1, Prop. 2]: a feasible linear system `Mξ = v` has a minimum-norm solution
(the sublevel set of the sup norm is compact), and a feasible point of sup norm `≤ 1` exists iff
that minimum exists and is `≤ 1`. An infeasible system has no `IsLeast`, which is the empty `min`.

## Inputs
* `ι` – row index type
* `h` – number of unknowns
* `M` – coefficient matrix
* `v` – right-hand side

## Hypotheses
* none

## Conclusion
* a unit-box solution exists iff a minimum-norm solution has norm at most one

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `Mξ = v` with `‖ξ‖∞ ≤ 1` exists iff the minimum of `‖ξ‖∞` over `Mξ = v` does
and is `≤ 1`. -/
theorem ConZonotope.exists_feasible_iff_isLeast {ι : Type} [Fintype ι] {h : ℕ}
    (M : Matrix ι (Fin h) ℝ) (v : ι → ℝ) : -- --- CONCL ---
    (∃ ξ : Fin h → ℝ, M *ᵥ ξ = v ∧ ∀ j, |ξ j| ≤ 1) ↔
      ∃ m, IsLeast {t | ∃ ξ : Fin h → ℝ, M *ᵥ ξ = v ∧ t = ‖ξ‖} m ∧ m ≤ 1 := by -- --- PROOF ---
  -- `‖ξ‖ ≤ 1` is the box `|ξⱼ| ≤ 1` the coefficients satisfy
  have hnorm : ∀ ξ : Fin h → ℝ, ‖ξ‖ ≤ 1 ↔ ∀ j, |ξ j| ≤ 1 := fun ξ => by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    simp only [Real.norm_eq_abs]
  simp only [← hnorm]
  constructor
  · rintro ⟨ξ₀, hξ₀, hn₀⟩
    -- the feasible points within `‖ξ₀‖` of the origin form a nonempty compact set
    have hclosed : IsClosed {ξ : Fin h → ℝ | M *ᵥ ξ = v} :=
      isClosed_eq (Matrix.mulVecLin M).continuous_of_finiteDimensional continuous_const
    have hK : IsCompact ({ξ : Fin h → ℝ | M *ᵥ ξ = v} ∩ Metric.closedBall 0 ‖ξ₀‖) :=
      (isCompact_closedBall 0 ‖ξ₀‖).inter_left hclosed
    obtain ⟨ξ₁, ⟨hξ₁, hb₁⟩, hmin⟩ := hK.exists_isMinOn ⟨ξ₀, hξ₀, by simp⟩
      continuous_norm.continuousOn
    have hle : ‖ξ₁‖ ≤ ‖ξ₀‖ := by simpa using hb₁
    refine ⟨‖ξ₁‖, ⟨⟨ξ₁, hξ₁, rfl⟩, ?_⟩, hle.trans hn₀⟩
    rintro t ⟨ξ, hξ, rfl⟩
    by_cases hξn : ‖ξ‖ ≤ ‖ξ₀‖
    · exact hmin ⟨hξ, by simpa using hξn⟩
    · exact hle.trans (not_le.mp hξn).le
  · rintro ⟨m, ⟨⟨ξ, hξ, rfl⟩, _⟩, hm⟩
    exact ⟨ξ, hξ, hm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
