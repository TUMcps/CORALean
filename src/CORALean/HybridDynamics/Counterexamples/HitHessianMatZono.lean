module

public import CORALean.HybridDynamics.Definitions.HitHessianNum
public import CORALean.HybridDynamics.Operations.HitHessianMatZono
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# With a factor per coordinate of `Θ/Λ`, [1, Prop. 3]'s matrix zonotope misses `Q⁽ⁱ⁾`

The proof of [1, Prop. 3] encloses `Θ_l(x₀)/Λ(x₀)` by `ψ_{c,l} ⊕ [-1, 1]ψ_{g,l}` coordinate by
coordinate, "using interval arithmetic", and [1, Prop. 3] then scales the whole of `ψ_g` by the
factor of the one generator `G̃^(i,1)`. In `ℝ²` with `A = [0 0; 1 -1]`, `b = (1, 0)`, `n = (0, 1)`,
`d = 1` and `R(0) = (2, 0) + [-1, 1](1, 0)`: `Λ = x₁ ∈ [1, 3]`, `Θ/Λ = (-1/Λ, 1/Λ - 1)`, enclosed
coordinatewise by `ψ_c = (-2/3, -1/3)`, `ψ_g = (1/3, 1/3)`; `Q⁽¹⁾ = Ω - 2(Θ/Λ)Υᵀ`, `Υ = (1, -1)`,
and the matrix zonotope is `{C̃ + κG̃^(1,1)}`, the other generators vanishing with `A`'s first row.
At `x₀ = (3, 0)`, `Θ/Λ = (-1/3, -2/3)`: entry `(1, 1)` forces `κ = 1`, entry `(2, 1)` forces
`κ = -1`. CORA's `guardIntersect_hyperplaneMap` takes `psi_g = rad(psi_int)` the same way.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the matrix zonotope misses the numerator at some state

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3] is false with its proof's coordinatewise enclosure of `Θ/Λ`: it holds on
`R(0)` and `Λ ≠ 0` there, yet `Q⁽¹⁾(x₀)` is outside the matrix zonotope for an `x₀ ∈ R(0)`. -/
theorem GuardMap.hitHessianMatZono_counterexample : -- --- CONCL ---
    ∃ (A : Mat ℝ 2 2) (b nv : Vec ℝ 2) (d : ℝ) (R₀ : Real.Zonotope (Vec ℝ 2)) (ψc ψg : Vec ℝ 2),
      (∀ x ∈ R₀.construct, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0) ∧
      (∀ x ∈ R₀.construct, ∀ l, |(-((nv ⬝ᵥ (A *ᵥ x + b)) • nv) - (d - nv ⬝ᵥ x) • (nv ᵥ* A)) l
          / (nv ⬝ᵥ (A *ᵥ x + b)) - ψc l| ≤ ψg l) ∧
      ∃ x₀ ∈ R₀.construct, GuardMap.hitHessianNum A b nv d x₀ 0
        ∉ (GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg 0).construct := by -- --- PROOF ---
  refine ⟨Matrix.of ![![0, 0], ![1, -1]], ![1, 0], ![0, 1], 1, ⟨1, ![2, 0], ![![1, 0]]⟩,
    ![-2/3, -1/3], ![1/3, 1/3], ?_, ?_, ?_⟩
  -- on `R(0)`, `x = (2 + β, 0)` and `Λ = 2 + β ∈ [1, 3]`
  · rintro _ ⟨β, hβ, rfl⟩
    have h := abs_le.mp (hβ 0)
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    linarith
  · rintro _ ⟨β, hβ, rfl⟩ l
    have h := abs_le.mp (hβ 0)
    have hΛ : (0 : ℝ) < 2 + β 0 := by linarith
    fin_cases l
    · simp [dotProduct, mulVec, vecMul, Fin.sum_univ_two]
      rw [abs_le]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hΛ]; nlinarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hΛ]; nlinarith
    · simp [dotProduct, mulVec, vecMul, Fin.sum_univ_two]
      rw [abs_le]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ hΛ]; nlinarith
      · rw [sub_le_iff_le_add, div_le_iff₀ hΛ]; nlinarith
  -- at `x₀ = (3, 0)`, two entries ask for opposite factors
  · refine ⟨![3, 0], ⟨![1], fun j => by fin_cases j; simp, ?_⟩, ?_⟩
    · ext j; fin_cases j <;> simp; norm_num
    · rintro ⟨β, -, h⟩
      erw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one] at h
      simp only [GuardMap.hitHessianMatZono, Fin.append_left, Fin.append_right] at h
      have h00 := congrFun (congrFun h 0) 0
      have h10 := congrFun (congrFun h 1) 0
      simp [GuardMap.hitHessianNum, dotProduct, mulVec, vecMul, Fin.sum_univ_two,
        vecMulVec] at h00 h10
      norm_num at h00 h10
      linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
