import CORALean.HybridDynamics.Definitions.HitHessianNum
import CORALean.HybridDynamics.Operations.HitHessianMatZono
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic

/-!
# The matrix zonotope of [1, Prop. 3] encloses `Q⁽ⁱ⁾`, with one factor for `Θ/Λ`

[1, Prop. 3]: `Q⁽ⁱ⁾(x₀) ∈ (C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` for `x₀ ∈ R(0)`, provided the vector
`Θ(x₀)/Λ(x₀)` lies in the one-generator zonotope `ψ_c ⊕ [-1, 1]ψ_g`: a single factor `κ`
for all its coordinates, which the one generator `G̃^(i,1)` requires. With
`x₀ = c_x + ∑ β_α g_x^(α)`,
`Θ` and `(Ax₀ + b)ᵢ` are affine in `β`, and `Q⁽ⁱ⁾(x₀)` is `C̃⁽ⁱ⁾ + κG̃^(i,1)` plus `β_α` times
`G̃^(i,1+α)` plus `κβ_α` times `G̃^(i,1+p+α)`. The proof's (19) encloses each coordinate by interval
arithmetic, a factor per coordinate; `GuardMap.hitHessianMatZono_counterexample` shows that
this is not enough. [1, Sec. 5.4] feeds these matrix zonotopes to [1, Thm. 1].

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3]: `Q⁽ⁱ⁾(x₀)` lies in the matrix zonotope, for `x₀ ∈ R(0)` with
`Θ(x₀)/Λ(x₀) = ψ_c + κψ_g`, `|κ| ≤ 1`. -/
theorem GuardMap.hitHessianNum_mem_hitHessianMatZono (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ)
    (R₀ : Real.Zonotope (Vec ℝ n)) (ψc ψg : Vec ℝ n) (i : Fin n) {x₀ : Vec ℝ n}
    (hx₀ : x₀ ∈ R₀.construct) {κ : ℝ} (hκ : |κ| ≤ 1)
    (hψ : (nv ⬝ᵥ (A *ᵥ x₀ + b))⁻¹ •
      (-((nv ⬝ᵥ (A *ᵥ x₀ + b)) • nv) - (d - nv ⬝ᵥ x₀) • (nv ᵥ* A)) = ψc + κ • ψg) :
    GuardMap.hitHessianNum A b nv d x₀ i
      ∈ (GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg i).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx₀
  set Λ : ℝ := nv ⬝ᵥ (A *ᵥ (R₀.c + ∑ j, β j • R₀.G j) + b) with hΛdef
  set Υ : Vec ℝ n := nv ᵥ* A with hΥdef
  -- the factors: `κ`, then `β_α`, then `κβ_α`
  refine ⟨Fin.append (Fin.append ![κ] β) (fun α => κ * β α), fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
      · rw [Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
      · rw [Fin.append_left, Fin.append_right]; exact hβ α
    · rw [Fin.append_right, abs_mul]
      exact mul_le_one₀ hκ (abs_nonneg _) (hβ α)
  -- `Θ/Λ` and `(Ax₀ + b)ᵢ` in the factors
  have hψl : ∀ l, (-(Λ • nv) - (d - nv ⬝ᵥ (R₀.c + ∑ j, β j • R₀.G j)) • Υ) l / Λ
      = ψc l + κ * ψg l := fun l => by
    have h := congrFun hψ l
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h
    rw [div_eq_inv_mul, h]
  have hf : (A *ᵥ (R₀.c + ∑ j, β j • R₀.G j) + b) i
      = (A *ᵥ R₀.c) i + b i + ∑ j, β j * (A *ᵥ R₀.G j) i := by
    rw [mulVec_add, mulVec_sum]
    simp only [Pi.add_apply, Finset.sum_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    ring
  -- `Λ`, `nᵀx₀` and `Θ(x₀)` in the factors
  have e1 : Λ = nv ⬝ᵥ (A *ᵥ R₀.c + b) + ∑ j, β j * (nv ⬝ᵥ (A *ᵥ R₀.G j)) := by
    rw [hΛdef, mulVec_add, mulVec_sum, add_right_comm, dotProduct_add, dotProduct_sum]
    simp only [mulVec_smul, dotProduct_smul, smul_eq_mul]
  have e2 : nv ⬝ᵥ (R₀.c + ∑ j, β j • R₀.G j) = nv ⬝ᵥ R₀.c + ∑ j, β j * (nv ⬝ᵥ R₀.G j) := by
    rw [dotProduct_add, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  have hΘ : ∀ m, (-(Λ • nv) - (d - nv ⬝ᵥ (R₀.c + ∑ j, β j • R₀.G j)) • Υ) m
      = (-((nv ⬝ᵥ (A *ᵥ R₀.c + b)) • nv) - (d - nv ⬝ᵥ R₀.c) • Υ) m
        + ∑ j, β j * (-((nv ⬝ᵥ (A *ᵥ R₀.G j)) • nv) + (nv ⬝ᵥ R₀.G j) • Υ) m := by
    intro m
    have e3 : ∑ j, β j * (-((nv ⬝ᵥ (A *ᵥ R₀.G j)) • nv) + (nv ⬝ᵥ R₀.G j) • Υ) m
        = -((∑ j, β j * (nv ⬝ᵥ (A *ᵥ R₀.G j))) * nv m)
          + (∑ j, β j * (nv ⬝ᵥ R₀.G j)) * Υ m := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e3, e2, e1]
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- the three blocks of factors, then entry by entry
  simp only [GuardMap.hitHessianMatZono]
  erw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Fin.append_left, Fin.append_right, Matrix.cons_val_zero]
  ext l m
  simp only [GuardMap.hitHessianNum, Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, ← hΛdef]
  rw [hψl l, hΘ m, hΘ l, hf, hΥdef]
  -- both sides as sums of the same products
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_mul, mul_neg, Finset.sum_neg_distrib]
  ring_nf

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
