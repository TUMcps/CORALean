module

public import CORALean.ContSet.Zonotope.Real.Theorems.RightInvReach

@[expose] public section

/-!
# A zonotope inside another, from approximate coefficients and a reached box

The Sadraddini-Tedrake certificate `G₁ = G₂ Γ`, `c₂ - c₁ = G₂ β₀`, `|Γ|₁ + |β₀| ≤ 1` made robust to
the rounding a float layer cannot avoid: `Γ` and `β₀` only approximate the solutions, and the
residuals `G₁ - G₂ Γ`, `c₁ - e₂ - c₂ - G₂ β₀` and the first set's error `e₁` only have to fit in
the box of vectors a checked right inverse of `G₂` reaches (`Zonotope.rightInv_reach`), with
coefficients of size at most `δ` that the coefficient budget `|β₀ₖ| + ∑ⱼ |Γₖⱼ| + δ ≤ 1` pays for.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n h₁ h₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.contains_via_reach (G₁ : Mat ℝ n h₁) (G₂ : Mat ℝ n h₂) (Γ : Mat ℝ h₂ h₁)
    (β₀ : Vec ℝ h₂) (c₁ c₂ e₁ e₂ : Vec ℝ n) {B δ : ℝ}
    (hreach : ∀ d : Vec ℝ n, (∀ i, |d i| ≤ B) → ∃ β' : Vec ℝ h₂, G₂ *ᵥ β' = d ∧ ∀ k, |β' k| ≤ δ)
    (hres : ∀ i, |c₁ i - e₂ i - (c₂ i + (G₂ *ᵥ β₀) i)| + ∑ j, |(G₁ - G₂ * Γ) i j| + |e₁ i| ≤ B)
    (hcoef : ∀ k, |β₀ k| + ∑ j, |Γ k j| + δ ≤ 1) (β : Vec ℝ h₁)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    ∃ γ : Vec ℝ h₂, (∀ k, |γ k| ≤ 1) ∧
      c₁ + G₁ *ᵥ β + e₁ = e₂ + (c₂ + G₂ *ᵥ γ) := by -- --- PROOF ---
  -- the part of the first set's point the coefficients `Γ β` and `β₀` do not explain
  set d : Vec ℝ n := c₁ + G₁ *ᵥ β + e₁ - e₂ - (c₂ + G₂ *ᵥ β₀) - G₂ *ᵥ (Γ *ᵥ β) with hd
  have hdi : ∀ i, d i = (c₁ i - e₂ i - (c₂ i + (G₂ *ᵥ β₀) i)) + ((G₁ - G₂ * Γ) *ᵥ β) i + e₁ i := by
    intro i
    simp only [hd, Pi.add_apply, Pi.sub_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    ring
  have hdB : ∀ i, |d i| ≤ B := by
    intro i
    have h1 : |((G₁ - G₂ * Γ) *ᵥ β) i| ≤ ∑ j, |(G₁ - G₂ * Γ) i j| := by
      calc |((G₁ - G₂ * Γ) *ᵥ β) i| = |∑ j, (G₁ - G₂ * Γ) i j * β j| := rfl
        _ ≤ ∑ j, |(G₁ - G₂ * Γ) i j * β j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |(G₁ - G₂ * Γ) i j| := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)
    rw [hdi i]
    have h2 := abs_add_le (c₁ i - e₂ i - (c₂ i + (G₂ *ᵥ β₀) i)) (((G₁ - G₂ * Γ) *ᵥ β) i)
    have h3 := abs_add_le (c₁ i - e₂ i - (c₂ i + (G₂ *ᵥ β₀) i) + ((G₁ - G₂ * Γ) *ᵥ β) i) (e₁ i)
    linarith [hres i]
  obtain ⟨β', hβ', hβδ⟩ := hreach d hdB
  refine ⟨β₀ + Γ *ᵥ β + β', fun k => ?_, ?_⟩
  · -- the coefficient budget
    have h2 : |(Γ *ᵥ β) k| ≤ ∑ j, |Γ k j| := by
      calc |(Γ *ᵥ β) k| = |∑ j, Γ k j * β j| := rfl
        _ ≤ ∑ j, |Γ k j * β j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |Γ k j| := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hβ j)
    have h3 := abs_add_le (β₀ k + (Γ *ᵥ β) k) (β' k)
    have h4 := abs_add_le (β₀ k) ((Γ *ᵥ β) k)
    simp only [Pi.add_apply]
    linarith [hcoef k, hβδ k]
  · -- the point
    funext i
    have hi := congrFun hβ' i
    have hdi' : d i = (c₁ + G₁ *ᵥ β + e₁ - e₂ - (c₂ + G₂ *ᵥ β₀) - G₂ *ᵥ (Γ *ᵥ β)) i := by
      simp [hd]
    simp only [Pi.add_apply, Pi.sub_apply] at hdi' ⊢
    have hmv : (G₂ *ᵥ (β₀ + Γ *ᵥ β + β')) i
        = (G₂ *ᵥ β₀) i + (G₂ *ᵥ (Γ *ᵥ β)) i + (G₂ *ᵥ β') i := by
      simp [Matrix.mulVec_add]
    rw [hmv, hi]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
