module

public import CORALean.ContSet.ProbZonotope.Real.Operations.ConfidenceZonotope
public import CORALean.ContSet.ProbZonotope.Real.Definitions.GZonotopeLaw
public import CORALean.ContSet.ProbZonotope.Real.Theorems.StdGaussianBox
public import CORALean.ContSet.Zonotope.Real.Theorems.Basic

@[expose] public section

/-!
# The confidence set holds the G-zonotope with probability `erf(m/√2)ⁿ`

[1, Prop. 2]: the realizations of `G N` lie in `η(𝒵, m) = (0, m G)` with probability
`erf(m/√2)ⁿ`, written here as `P[-m ≤ N(0, 1) ≤ m]ⁿ` — the identity
`P[-m < N(0, 1) < m] = erf(m/√2)` that [1] quotes as well known; Mathlib has no `erf`. For
`m > 0` and `G` invertible, `Gβ ∈ (0, m G)` exactly when `β` is in the cube `[-m, m]ⁿ`
(`stdGaussian_cube`). [1] chooses `n` generators "without loss of generality"; that they are
independent, `det G ≠ 0`, is what makes the probability exact rather than a lower bound.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem confidenceZonotope_prob (G : Mat ℝ n n) (hG : G.det ≠ 0) {m : ℝ} (hm : 0 < m) :
    gZonotopeLaw 0 G (toLp 2 '' (confidenceZonotope G m).construct)
      = (gaussianReal 0 1 (Set.Icc (-m) m)) ^ n := by -- --- PROOF ---
  have hS : MeasurableSet (toLp 2 '' (confidenceZonotope G m).construct) := by
    rw [show toLp 2 '' (confidenceZonotope G m).construct
        = ofLp ⁻¹' (confidenceZonotope G m).construct from by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨ofLp x, hx, rfl⟩]
    exact (Zonotope.isClosed_construct _).measurableSet.preimage (by fun_prop)
  rw [gZonotopeLaw, Measure.map_apply (by fun_prop) hS, ← stdGaussian_cube m]
  congr 1
  -- `Gβ` is in the zonotope exactly when `β` is in the cube
  have hsum : ∀ α : Fin (confidenceZonotope G m).h → ℝ,
      (confidenceZonotope G m).c + ∑ j, α j • (confidenceZonotope G m).G j = G *ᵥ (m • α) := by
    intro α; funext i
    simp only [confidenceZonotope, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by
      change α j * (m * G i j) = G i j * (m * α j); ring
  have hinj : Function.Injective (G *ᵥ ·) := by
    intro x y hxy
    have := congrArg (G⁻¹ *ᵥ ·) hxy
    simpa [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG)] using this
  ext β
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- `Gβ = G(mα)` forces `β = mα`
    rintro ⟨x, ⟨α, hα, hx⟩, hxβ⟩
    have hxβ' : x = 0 + G *ᵥ ofLp β := by simpa using congrArg ofLp hxβ
    rw [hsum, hxβ', zero_add] at hx
    have hβ := hinj hx
    intro i
    have := congrFun hβ i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    have hαi := abs_le.1 (hα i)
    constructor <;> nlinarith [hαi.1, hαi.2]
  · -- `β = m (β/m)` with `β/m` in the unit cube
    intro hβ
    refine ⟨0 + G *ᵥ ofLp β, ⟨fun j => ofLp β j / m, fun j => ?_, ?_⟩, rfl⟩
    · rw [abs_div, abs_of_pos hm, div_le_one hm]
      exact abs_le.2 (hβ j)
    · rw [hsum, zero_add]
      congr 1
      funext j
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
