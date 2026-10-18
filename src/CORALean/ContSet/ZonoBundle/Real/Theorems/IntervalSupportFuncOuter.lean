module

public import CORALean.ContSet.ZonoBundle.Real.Operations.IntervalSupportFunc
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ContSet.Theorems.SupportFuncLeCoeIff
public import CORALean.ContSet.SetIntersection.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `ZonoBundle.intervalSupportFunc` encloses the bundle

A bundle of at least one member is compact, so every coordinate is bounded on it and its support
function in `±eᵢ` is finite: each point reads at most the support value in `eᵢ` and at least the
negated one in `-eᵢ`, which are the box's two ends.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The support-function box contains the bundle. -/
theorem ZonoBundle.intervalSupportFunc_outer (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct ⊆ zB.intervalSupportFunc.construct := by -- --- PROOF ---
  intro x hx i
  -- every linear functional is bounded above on the compact bundle
  have hc : IsCompact zB.construct :=
    SetIntersection.isCompact_construct (I := zB.toSetIntersection)
      (List.ofFn_eq_nil_iff.not.mpr hk.ne')
  have hle : ∀ ℓ : Vec ℝ n →ₗ[ℝ] ℝ, Continuous ℓ → ℓ x ≤ (supportFunc zB.construct ℓ).toReal := by
    intro ℓ hℓ
    obtain ⟨M, hM⟩ := hc.bddAbove_image hℓ.continuousOn
    have hbd : supportFunc zB.construct ℓ ≤ (M : EReal) :=
      supportFunc_le_coe_iff.mpr fun y hy => hM ⟨y, hy, rfl⟩
    have h := EReal.toReal_le_toReal (le_iSup₂_of_le x hx le_rfl : (ℓ x : EReal) ≤ _)
      (EReal.coe_ne_bot _) (ne_top_of_le_ne_top (EReal.coe_ne_top M) hbd)
    rwa [EReal.toReal_coe] at h
  -- the two ends, the lower one through the negated direction
  have hup := hle (LinearMap.proj i) (continuous_apply i)
  have hlo := hle (-LinearMap.proj i) (continuous_apply i).neg
  simp only [LinearMap.neg_apply, LinearMap.proj_apply] at hup hlo
  exact ⟨by show -_ ≤ x i; linarith, hup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
