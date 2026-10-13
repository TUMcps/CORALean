import CORALean.Global.ShenmaierHalfspace
import CORALean.Global.EllipsotopeSupport

/-!
# Halfspace sampling's `False` is certain

`[1, Thm. 4.3]`, first half, for `[1, Alg. 2]`: `Ê ⊄ E` if `r_Shs > 1`. Each `r_{Shs,i}`
is the support of `Ê - d` in the direction `zᵢ` (`[1, Eq. 19]`), so some `x ∈ Ê` has
`zᵢ(x - d) > 1`; a point `d + Hβ` of `E` has `zᵢ(Hβ) ≤ ‖Hᵀzᵢ‖_{q*} ‖β‖ ≤ 1`. Only
`zᵢ` in the dual set is used, not that it maximizes anything, nor how the samples came.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E₁ E₂ V : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- =======================================  MAIN THEOREM  ======================================= --

theorem shenmaierHalfspace_eq_none_not_subset (G : E₁ →ₗ[ℝ] V) (c : V) (H : E₂ →ₗ[ℝ] V)
    (d : V) {N : ℕ} (hN : 0 < N) (z : Fin N → V →L[ℝ] ℝ)
    (hz : ∀ i, ‖(z i).comp (LinearMap.toContinuousLinearMap H)‖ ≤ 1) (ϑ : ℝ)
    (h : shenmaierHalfspace G c d hN z ϑ = none) :
    ¬ {x | ∃ α : E₁, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆
      {x | ∃ β : E₂, ‖β‖ ≤ 1 ∧ x = d + H β} := by -- --- PROOF ---
  have hgt : shenmaierHalfspaceValue G c d hN z > 1 := by
    unfold shenmaierHalfspace at h
    simp only at h
    split_ifs at h with hv
    exact hv
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    fun i => ‖(z i).comp (LinearMap.toContinuousLinearMap G)‖ + z i (c - d)
  -- the support of `Ê - d` along `zᵢ` is attained at some `c - d + G α`
  obtain ⟨⟨_, ⟨α, hα, rfl⟩, hαe⟩, -⟩ := isGreatest_support_ellipsotope G (c - d) (z i)
  intro hsub
  obtain ⟨β, hβ, he⟩ := hsub ⟨α, hα, rfl⟩
  have hHβ : z i (H β) ≤ 1 := by
    have := ((z i).comp (LinearMap.toContinuousLinearMap H)).le_opNorm β
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toContinuousLinearMap'] at this
    exact (le_abs_self _).trans (this.trans (mul_le_one₀ (hz i) (norm_nonneg _) hβ))
  have : z i (c - d + G α) = z i (H β) := by
    rw [show c - d + G α = H β by rw [sub_add_eq_add_sub, he]; abel]
  unfold shenmaierHalfspaceValue at hgt
  simp only at hgt
  rw [hi, ← hαe] at hgt
  simp only at hgt
  rw [this] at hgt
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
