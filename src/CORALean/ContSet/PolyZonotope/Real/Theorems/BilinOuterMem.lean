import CORALean.ContSet.PolyZonotope.Real.Operations.BilinOuter
import CORALean.ContSet.PolyZonotope.Real.Theorems.AbsMonomialLeOne
import CORALean.ContSet.PolyZonotope.Real.Theorems.BilinPoint
import Mathlib.Tactic.Abel

/-!
# `bilinOuter` encloses the product of the two sets at shared factors

At one factor vector `a` and independent coefficients `β₁`, `β₂`, the product
`f (P + U₁) (Q + U₂) = f P Q + f U₁ Q + f U₁ U₂ + f P U₂` is a point of the result: `f P Q` is
`bilin_point`, and each other term is a block of `bilinGI`, with coefficients `β₁ j · mₗ`,
`β₁ j · β₂ l` and `mₗ · β₂ j` (`mₗ` the extended monomials), all in `[-1, 1]`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
  [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.bilinOuter_mem (f : α →ₗ[ℝ] β →ₗ[ℝ] γ) (pZ₁ : PolyZonotope α)
    (pZ₂ : PolyZonotope β) (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (β₁ : Fin pZ₁.q → ℝ) (β₂ : Fin pZ₂.q → ℝ) (hβ₁ : ∀ j, |β₁ j| ≤ 1) (hβ₂ : ∀ j, |β₂ j| ≤ 1) :
    f (pZ₁.point a + ∑ j, β₁ j • pZ₁.GI j)
        (pZ₂.point (fun k => a (Fin.cast hp.symm k)) + ∑ j, β₂ j • pZ₂.GI j)
      ∈ (pZ₁.bilinOuter f pZ₂ hp).construct := by -- --- PROOF ---
  -- `f` at two sums of scaled generators, expanded over the pairs
  have hexp : ∀ {r s : ℕ} (u : Fin r → α) (v : Fin s → β) (x : Fin r → ℝ) (y : Fin s → ℝ),
      f (∑ j, x j • u j) (∑ l, y l • v l) = ∑ j, ∑ l, (x j * y l) • f (u j) (v l) := by
    intro r s u v x y
    rw [map_sum f (fun j => x j • u j) Finset.univ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_smul]
  -- the coefficients of the new generators are products of numbers in `[-1, 1]`
  have hmul : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |x * y| ≤ 1 := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_one₀ hx (abs_nonneg _) hy
  have ha' : ∀ k, |(fun k => a (Fin.cast hp.symm k)) k| ≤ 1 := fun k => ha _
  have hm₁ : ∀ i, |pZ₁.extM a i| ≤ 1 := PolyZonotope.abs_monomial_le_one _ ha
  have hm₂ : ∀ i, |pZ₂.extM (fun k => a (Fin.cast hp.symm k)) i| ≤ 1 :=
    PolyZonotope.abs_monomial_le_one _ ha'
  have hP := PolyZonotope.sum_ext_eq_point pZ₁ a
  have hQ := PolyZonotope.sum_ext_eq_point pZ₂ (fun k => a (Fin.cast hp.symm k))
  -- the same factors `a`; the new coefficients are `β₁ · m`, `β₁ · β₂` and `m · β₂`
  refine ⟨a, Fin.append (Fin.append
      (fun l => β₁ (finProdFinEquiv.symm l).1 *
        pZ₂.extM (fun k => a (Fin.cast hp.symm k)) (finProdFinEquiv.symm l).2)
      (fun l => β₁ (finProdFinEquiv.symm l).1 * β₂ (finProdFinEquiv.symm l).2))
      (fun l => pZ₁.extM a (finProdFinEquiv.symm l).1 * β₂ (finProdFinEquiv.symm l).2),
    ha, ?_, ?_⟩
  · intro t
    refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · simpa only [Fin.append_left] using hmul _ _ (hβ₁ _) (hm₂ _)
      · simpa only [Fin.append_left, Fin.append_right] using hmul _ _ (hβ₁ _) (hβ₂ _)
    · simpa only [Fin.append_right] using hmul _ _ (hm₁ _) (hβ₂ _)
  · -- the point is `f P Q` and the block sums are the three cross terms
    show _ = (pZ₁.bilin f pZ₂ hp).point a + ∑ t : Fin (pZ₁.q * (pZ₂.h + 1) +
      pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q), _ • PolyZonotope.bilinGI f pZ₁ pZ₂ t
    rw [PolyZonotope.bilin_point]
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [PolyZonotope.bilinGI, Fin.append_left, Fin.append_right]
    -- each block is one cross term: `f U₁ Q`, `f U₁ U₂`, `f P U₂`
    have hA := hexp pZ₁.GI pZ₂.extG β₁ (pZ₂.extM fun k => a (Fin.cast hp.symm k))
    have hB := hexp pZ₁.GI pZ₂.GI β₁ β₂
    have hC := hexp pZ₁.extG pZ₂.GI (pZ₁.extM a) β₂
    rw [hQ] at hA
    rw [hP] at hC
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun pr : Fin pZ₁.q × Fin (pZ₂.h + 1) =>
        (β₁ pr.1 * pZ₂.extM (fun k => a (Fin.cast hp.symm k)) pr.2) •
          f (pZ₁.GI pr.1) (pZ₂.extG pr.2)),
      Equiv.sum_comp finProdFinEquiv.symm (fun pr : Fin pZ₁.q × Fin pZ₂.q =>
        (β₁ pr.1 * β₂ pr.2) • f (pZ₁.GI pr.1) (pZ₂.GI pr.2)),
      Equiv.sum_comp finProdFinEquiv.symm (fun pr : Fin (pZ₁.h + 1) × Fin pZ₂.q =>
        (pZ₁.extM a pr.1 * β₂ pr.2) • f (pZ₁.extG pr.1) (pZ₂.GI pr.2)),
      Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← hA, ← hB, ← hC]
    simp only [PolyZonotope.point, map_add, LinearMap.add_apply]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
