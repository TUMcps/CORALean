module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.ProbZonotope.Float.Operations.Basic
public import CORALean.ContSet.ProbZonotope.Real.Theorems.AbsSqrtMulVecLe
public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# The float confidence zonotope contains the exact one

For a law `N(μ, Σ)` of the float probabilistic zonotope (`μ` in the mean zonotope, `Σ` positive
semidefinite in the covariance interval), the exact confidence set `zonotope(probZ, m)` of the
probabilistic zonotope with the point mean `μ` and covariance `Σ` lies in the float
`ProbZonotope.zonotope`, for every `m` up to the float one. The exact set is `μ + m g [-1, 1]ⁿ`
with `g` the square root of `Σ`, whose coordinate `i` reaches `m √(n Σᵢᵢ)` at most
(`abs_sqrt_mulVec_le`), under the rounded-up radius `confidenceRadius`; the box of that radius is
inside its diagonal-generator zonotope, and the sum with the mean zonotope is `plus_outer`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic
open scoped Matrix MatrixOrder Pointwise

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.zonotope_outer (p : ℕ) (P : ProbZonotope 𝕋 n) (M : 𝕋) {μ : Vec ℝ n}
    (hμ : μ ∈ P.Z.construct) {S : Mat ℝ n n} (hS : S ∈ P.cov.construct) (hpsd : S.PosSemidef)
    {m : ℝ} (hm : 0 ≤ m) (hmM : m ≤ toReal M) :
    (Real.ProbZonotope.zonotope ⟨⟨0, μ, fun j => j.elim0⟩, S⟩ m).construct
      ⊆ (P.zonotope p M).construct := by -- --- PROOF ---
  intro x hx
  rw [Real.ProbZonotope.zonotope, ← Real.Zonotope.plus_exact] at hx
  obtain ⟨a, ha, y, hy, rfl⟩ := hx
  -- the point mean is `μ`
  obtain ⟨_, _, hai⟩ := Real.Zonotope.mem_construct_iff.mp ha
  have haμ : a = μ := funext fun i => by simpa using hai i
  subst haμ
  -- the exact offset: coordinate `k` is `m` times a coordinate of `g β`
  obtain ⟨γ, hγ, hyk⟩ := Real.Zonotope.mem_construct_iff.mp hy
  have hyk' : ∀ k, y k = m * (CFC.sqrt S *ᵥ γ) k := fun k => by
    rw [hyk k]
    simp only [Real.confidenceZonotope, Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- it is under the radius: coordinate `k` of `m g β` is at most `m √(n Σₖₖ)`, rounded up
  have hbox : y ∈ (⟨(-(P.confidenceRadius p M)), P.confidenceRadius p M⟩ :
      Interval (Vec 𝕋 n)).construct := fun k => by
    have hSkk : S k k ≤ toReal (P.cov.sup k k) := (Interval.mem_mat_iff.mp hS k k).2
    have hacc := Real.ProbZonotope.abs_sqrt_mulVec_le hpsd hγ k
    -- `n Σₖₖ` is under the rounded count of the upper diagonal, its root under `sqrtUp`
    have h0 : (n : ℝ) * S k k ≤ toReal (nsmulUp n (maximum zero (P.cov.sup k k))) := by
      refine le_trans ?_ (le_nsmulUp n _)
      rw [toReal_maximum, toReal_zero]
      exact mul_le_mul_of_nonneg_left (le_trans hSkk (le_max_right _ _)) (Nat.cast_nonneg n)
    have h1 := le_trans (Real.sqrt_le_sqrt h0)
      (le_sqrtUp p (nsmulUp n (maximum zero (P.cov.sup k k))))
    have h2 := mul_le_mulUp M (sqrtUp p (nsmulUp n (maximum zero (P.cov.sup k k))))
    have h3 : m * Real.sqrt (n * S k k) ≤ toReal (P.confidenceRadius p M k) := by
      refine le_trans ?_ h2
      exact mul_le_mul hmM h1 (Real.sqrt_nonneg _) (le_trans hm hmM)
    have h4 : |y k| ≤ toReal (P.confidenceRadius p M k) := by
      rw [hyk' k, abs_mul, abs_of_nonneg hm]
      exact le_trans (mul_le_mul_of_nonneg_left hacc hm) h3
    rw [abs_le] at h4
    exact ⟨by show toReal (neg _) ≤ y k; rw [toReal_neg]; exact h4.1, h4.2⟩
  exact Zonotope.plus_outer _ _ (Set.add_mem_add hμ (Interval.zonotope_contains _ hbox))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
