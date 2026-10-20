module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.IntervalSupportFuncOuter
public import CORALean.ContSet.ZonoBundle.Real.Operations.Box

@[expose] public section

/-!
# `ZonoBundle.intervalSupportFunc` is the bundle's bounding box

The support value in `eᵢ` is the least upper bound of the `i`-th coordinate over the bundle, so
any box holding the bundle has its upper end above it, and likewise below: the support-function
box lies in every box that holds the bundle, and holds the bundle itself
(`intervalSupportFunc_outer`). It is therefore the least such box, `ZonoBundle.box`. For a
nonempty bundle: the support function of the empty set is `-∞`, read as `0`.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – the bundle has a member
* `hne` – the bundle is nonempty

## Conclusion
* the support-function box is the tightest box of the bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The support-function box of a nonempty bundle is its bounding box, exactly. -/
theorem ZonoBundle.intervalSupportFunc_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k)
    (hne : zB.construct.Nonempty) : zB.intervalSupportFunc.construct = zB.box := by -- --- PROOF ---
  obtain ⟨y₀, hy₀⟩ := hne
  -- a bound on a coordinate over the bundle bounds its support value, the bundle having a point
  have hle : ∀ (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (b : ℝ), (∀ y ∈ zB.construct, ℓ y ≤ b) →
      (supportFunc zB.construct ℓ).toReal ≤ b := by
    intro ℓ b hb
    have h := EReal.toReal_le_toReal (supportFunc_le_coe_iff.mpr hb)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot (ℓ y₀)) (le_iSup₂_of_le y₀ hy₀ le_rfl))
      (EReal.coe_ne_top b)
    rwa [EReal.toReal_coe] at h
  refine Set.Subset.antisymm (fun x hx => Set.mem_iInter.mpr fun I j => ?_)
    (Set.iInter_subset_of_subset ⟨_, zB.intervalSupportFunc_outer hk⟩ subset_rfl)
  -- each end of the support box lies inside the ends of any box holding the bundle
  have hI : ∀ y ∈ zB.construct, I.1.inf j ≤ y j ∧ y j ≤ I.1.sup j := fun y hy => I.2 hy j
  have hup := hle (LinearMap.proj j) (I.1.sup j) fun y hy => (hI y hy).2
  have hlo := hle (-LinearMap.proj j) (-I.1.inf j) fun y hy => by
    simp only [LinearMap.neg_apply, LinearMap.proj_apply, neg_le_neg_iff]
    exact (hI y hy).1
  obtain ⟨hx₁, hx₂⟩ := hx j
  change -(supportFunc zB.construct (-LinearMap.proj j)).toReal ≤ x j at hx₁
  change x j ≤ (supportFunc zB.construct (LinearMap.proj j)).toReal at hx₂
  show I.1.inf j ≤ x j ∧ x j ≤ I.1.sup j
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
