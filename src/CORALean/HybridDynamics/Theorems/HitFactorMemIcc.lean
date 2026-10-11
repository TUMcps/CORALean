import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono
import CORALean.ContSet.Zonotope.Real.Theorems.Convex

/-!
# The shared remainder factor lies in the bounds of `1/Λ²`

`1/(Λ(ξ)Λ(x₀)) ∈ [φ̲, φ̄]` for `ξ`, `x₀` in a convex set `R(0)`, such as a zonotope, on which
`Λ(x) = nᵀ(Ax + b)` has no zero and `[φ̲, φ̄] ⊇ {1/Λ(x)²}`: `Λ` is affine and `R(0)` convex, so
`Λ` keeps one sign on it and `1/(Λ(ξ)Λ(x₀))` is the geometric mean of `1/Λ(ξ)²` and
`1/Λ(x₀)²`. The factor `φ` of the exact expansion `GuardMap.hitPoint_add_eq`, enclosed by
the interval `[φ̲, φ̄]` of [1, Prop. 3].

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

/-- `Λ` keeps its sign on `R(0)`, so `1/(Λ(ξ)Λ(x₀))` lies in `[φ̲, φ̄]`. -/
theorem GuardMap.hitFactor_mem_Icc (A : Mat ℝ n n) (b nv : Vec ℝ n) {R₀ : Set (Vec ℝ n)}
    (hR : Convex ℝ R₀) {φlo φhi : ℝ} (hΛ : ∀ x ∈ R₀, nv ⬝ᵥ (A *ᵥ x + b) ≠ 0)
    (hφ : ∀ x ∈ R₀, φlo ≤ 1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ∧
      1 / (nv ⬝ᵥ (A *ᵥ x + b)) ^ 2 ≤ φhi)
    {ξ x₀ : Vec ℝ n} (hξ : ξ ∈ R₀) (hx₀ : x₀ ∈ R₀) :
    φlo ≤ 1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) ∧
      1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b))) ≤ φhi := by -- --- PROOF ---
  -- same sign: else `Λ` vanishes on the segment, which lies in the convex `R(0)`
  have hpq : 0 < (nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ x₀ + b)) := by
    have hseg : ∀ t : ℝ, nv ⬝ᵥ (A *ᵥ (t • ξ + (1 - t) • x₀) + b)
        = t * (nv ⬝ᵥ (A *ᵥ ξ + b)) + (1 - t) * (nv ⬝ᵥ (A *ᵥ x₀ + b)) := fun t => by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    have hp0 := hΛ ξ hξ
    have hq0 := hΛ x₀ hx₀
    generalize nv ⬝ᵥ (A *ᵥ ξ + b) = p at *
    generalize nv ⬝ᵥ (A *ᵥ x₀ + b) = q at *
    rcases lt_or_gt_of_ne (mul_ne_zero hp0 hq0) with hneg | hpos
    · exfalso
      -- `t = q/(q - p)` puts `Λ` at zero on the segment
      have hqp : q - p ≠ 0 := fun h => by
        have : q = p := by linarith
        subst this; nlinarith [mul_self_nonneg q]
      have hsign : (0 < q ∧ p < 0) ∨ (q < 0 ∧ 0 < p) := by
        rcases lt_or_gt_of_ne hp0 with h | h
        · exact Or.inl ⟨by nlinarith, h⟩
        · exact Or.inr ⟨by nlinarith, h⟩
      -- `t ∈ [0, 1]` since `p`, `q` have opposite signs
      have ht0 : 0 ≤ q / (q - p) := by
        rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg h1.le (by linarith)
        · exact div_nonneg_of_nonpos h1.le (by linarith)
      have ht1 : 0 ≤ 1 - q / (q - p) := by
        have e : 1 - q / (q - p) = -p / (q - p) := by field_simp; ring
        rw [e]
        rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact div_nonneg (by linarith) (by linarith)
        · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      -- the zero is a point of `R(0)`, against `Λ ≠ 0` there
      have hmem : (q / (q - p)) • ξ + (1 - q / (q - p)) • x₀ ∈ R₀ :=
        hR hξ hx₀ ht0 ht1 (by ring)
      apply hΛ _ hmem
      rw [hseg]
      field_simp
      ring
    · exact hpos
  -- `1/(pq)` is the geometric mean of `1/p²` and `1/q²`
  obtain ⟨hlo₁, hhi₁⟩ := hφ ξ hξ
  obtain ⟨hlo₂, hhi₂⟩ := hφ x₀ hx₀
  have hp0 := hΛ ξ hξ
  have hq0 := hΛ x₀ hx₀
  generalize nv ⬝ᵥ (A *ᵥ ξ + b) = p at *
  generalize nv ⬝ᵥ (A *ᵥ x₀ + b) = q at *
  have hm : 0 < 1 / (p * q) := by positivity
  have hsq : (1 / (p * q)) ^ 2 = 1 / p ^ 2 * (1 / q ^ 2) := by field_simp
  have h1 : 0 ≤ 1 / p ^ 2 := by positivity
  have h2 : 0 ≤ 1 / q ^ 2 := by positivity
  -- the lower and the upper bound, by squaring
  constructor
  · by_contra h
    push Not at h
    have hlo : 0 < φlo := lt_trans hm h
    have e1 : (1 / (p * q)) ^ 2 < φlo ^ 2 := by gcongr
    have e2 : φlo ^ 2 ≤ 1 / p ^ 2 * (1 / q ^ 2) := by
      rw [sq φlo]; exact mul_le_mul hlo₁ hlo₂ hlo.le h1
    linarith
  · by_contra h
    push Not at h
    have h0 : 0 ≤ φhi := le_trans h1 hhi₁
    have e1 : φhi ^ 2 < (1 / (p * q)) ^ 2 := by gcongr
    have e2 : 1 / p ^ 2 * (1 / q ^ 2) ≤ φhi ^ 2 := by
      rw [sq φhi]; exact mul_le_mul hhi₁ hhi₂ h2 h0
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
