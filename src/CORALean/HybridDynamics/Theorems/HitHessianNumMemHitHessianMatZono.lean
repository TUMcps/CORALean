module

public import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono

@[expose] public section

/-!
# The matrix zonotope of [1, Prop. 3] encloses `Q⁽ⁱ⁾`, with one factor for `Θ/Λ`

[1, Prop. 3]: `Q⁽ⁱ⁾(x₀) ∈ (C̃⁽ⁱ⁾, G̃^(i,1), …, G̃^(i,1+2p))` for `x₀ ∈ R(0)`, provided the vector
`Θ(x₀)/Λ(x₀)` lies in the one-generator zonotope `ψ_c ⊕ [-1, 1]ψ_g`: a single factor `κ`
for all its coordinates, which the one generator `G̃^(i,1)` requires. With
`x₀ = c_x + ∑ β_α g_x^(α)`,
`Θ` and `(Ax₀ + b)ᵢ` are affine in `β`, and `Q⁽ⁱ⁾(x₀)` is `C̃⁽ⁱ⁾ + κG̃^(i,1)` plus `β_α` times
`G̃^(i,1+α)` plus `κβ_α` times `G̃^(i,1+p+α)`. The proof's (19) encloses each coordinate by interval
arithmetic, a factor per coordinate; `GuardMap.hitHessianMatZono_counterexample` shows that
this is not enough. The factors themselves are `GuardMap.hitHessianNum_eq_hitHessianMatZono`;
[1, Sec. 5.4] feeds these matrix zonotopes to [1, Thm. 1].

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
      (-((nv ⬝ᵥ (A *ᵥ x₀ + b)) • nv) - (d - nv ⬝ᵥ x₀) • (nv ᵥ* A)) = ψc + κ • ψg) : -- --- STMT ---
    GuardMap.hitHessianNum A b nv d x₀ i
      ∈ (GuardMap.hitHessianMatZono A b nv d R₀ ψc ψg i).construct := by -- --- PROOF ---
  obtain ⟨β, hβ, rfl⟩ := hx₀
  -- the factors: `κ`, then `β_α`, then `κβ_α`
  refine ⟨Fin.append (Fin.append ![κ] β) (fun α => κ * β α), fun j => ?_,
    GuardMap.hitHessianNum_eq_hitHessianMatZono A b nv d R₀ ψc ψg i β κ hψ⟩
  refine Fin.addCases (fun j => ?_) (fun α => ?_) j
  · refine Fin.addCases (fun j => ?_) (fun α => ?_) j
    · rw [Fin.append_left, Fin.append_left, Fin.fin_one_eq_zero j]; simpa using hκ
    · rw [Fin.append_left, Fin.append_right]; exact hβ α
  · rw [Fin.append_right, abs_mul]
    exact mul_le_one₀ hκ (abs_nonneg _) (hβ α)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
