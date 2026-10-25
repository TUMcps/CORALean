module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# A maximizer of the dual program whose columns differ

[1, Thm. 16 (parallelotope)] says that for `q = ∞` and `H` square and invertible, condition (34) is
"always satisfied": every maximizer `Y` of Eq. 33, `max tr(Gᵀ Y)` over `‖Hᵀ Y‖_{L⊤∞,1} ≤ 1`, has its
columns equal up to sign. At `G = H = I₂` the maximum is `1`, `y₁₁ + y₂₂ ≤ maxⱼ |y₁ⱼ| + maxⱼ |y₂ⱼ|`,
and `Y = e₁ e₁ᵀ` attains it with columns `(1, 0)` and `(0, 0)`. The proof finds the maximum at an
extreme point of the constraint set, which shows that some maximizer satisfies (34)
(`parallelotope_lr_exact`), not that every one does.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a maximizer of the dual program exists whose columns differ

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Y = e₁ e₁ᵀ` maximizes Eq. 33 at `G = H = I₂`, `q = ∞`, and its columns differ. -/
theorem parallelotope_lr_exact_counterexample : -- --- CONCL ---
    let G : Matrix (Fin 2) (Fin 2) ℝ := 1
    let H : Matrix (Fin 2) (Fin 2) ℝ := 1
    let Y : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0
    IsUnit H.det ∧ ∑ k, (⨆ j, |(Hᵀ * Y) k j|) ≤ 1 ∧
      (∀ Y' : Matrix (Fin 2) (Fin 2) ℝ, ∑ k, (⨆ j, |(Hᵀ * Y') k j|) ≤ 1 →
        trace (Gᵀ * Y') ≤ trace (Gᵀ * Y)) ∧
      ¬ ∀ j j', (fun k => Y k j) = (fun k => Y k j') ∨
        (fun k => Y k j) = -(fun k => Y k j') := by -- --- PROOF ---
  intro G H Y
  have hle : ∀ (Z : Matrix (Fin 2) (Fin 2) ℝ) (k j : Fin 2), |Z k j| ≤ ⨆ j, |Z k j| :=
    fun Z k j => le_ciSup (f := fun j => |Z k j|) (Set.finite_range _).bddAbove j
  refine ⟨by simp [H], ?_, fun Y' hY' => ?_, fun h => ?_⟩
  · simp only [H, transpose_one, Matrix.one_mul, Fin.sum_univ_two]
    have h0 : (⨆ j, |Y 0 j|) ≤ 1 := Real.iSup_le (fun j => by
      fin_cases j <;> simp [Y]) zero_le_one
    have h1 : (⨆ j, |Y 1 j|) ≤ 0 := Real.iSup_le (fun j => by simp [Y]) le_rfl
    linarith
  · simp only [H, G, transpose_one, Matrix.one_mul, Fin.sum_univ_two] at hY' ⊢
    have hY : trace Y = 1 := by simp [trace, Y]
    rw [hY]
    simp only [trace, diag, Fin.sum_univ_two]
    linarith [le_abs_self (Y' 0 0), le_abs_self (Y' 1 1), hle Y' 0 0, hle Y' 1 1]
  · rcases h 0 1 with h | h
    · have := congrFun h 0
      simp [Y] at this
    · have := congrFun h 0
      simp [Y] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
