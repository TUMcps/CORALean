module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# Every value between the corner products is a product

The image of the rectangle `[a, b] × [c, d]` under multiplication is connected, so it contains
everything between its least and greatest values; those are the extreme corner products. The
converse of `mul_between_corners`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.exists_mul_eq {a b c d z : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hz₁ : Interval.mulLo a b c d ≤ z) (hz₂ : z ≤ Interval.mulHi a b c d) :
    ∃ y x, (a ≤ y ∧ y ≤ b) ∧ (c ≤ x ∧ x ≤ d) ∧ y * x = z := by -- --- PROOF ---
  set S : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Set.Icc a b ×ˢ Set.Icc c d) with hSdef
  have hS : IsPreconnected S :=
    (isPreconnected_Icc.prod isPreconnected_Icc).image _ continuous_mul.continuousOn
  have mem : ∀ y x, a ≤ y → y ≤ b → c ≤ x → x ≤ d → y * x ∈ S :=
    fun y x h₁ h₂ h₃ h₄ => ⟨(y, x), ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩, rfl⟩
  have hmin : ∀ u v : ℝ, u ∈ S → v ∈ S → min u v ∈ S := fun u v hu hv => by
    rcases min_choice u v with h | h <;> rw [h] <;> assumption
  have hmax : ∀ u v : ℝ, u ∈ S → v ∈ S → max u v ∈ S := fun u v hu hv => by
    rcases max_choice u v with h | h <;> rw [h] <;> assumption
  have hac := mem a c le_rfl hab le_rfl hcd
  have had := mem a d le_rfl hab hcd le_rfl
  have hbc := mem b c hab le_rfl le_rfl hcd
  have hbd := mem b d hab le_rfl hcd le_rfl
  have hlo : Interval.mulLo a b c d ∈ S := hmin _ _ (hmin _ _ hac had) (hmin _ _ hbc hbd)
  have hhi : Interval.mulHi a b c d ∈ S := hmax _ _ (hmax _ _ hac had) (hmax _ _ hbc hbd)
  obtain ⟨⟨y, x⟩, ⟨⟨hy₁, hy₂⟩, ⟨hx₁, hx₂⟩⟩, hyx⟩ := hS.Icc_subset hlo hhi ⟨hz₁, hz₂⟩
  exact ⟨y, x, ⟨hy₁, hy₂⟩, ⟨hx₁, hx₂⟩, hyx⟩


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
