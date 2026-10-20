module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Float.Theorems.GetSubsetPointOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `ConPolyZono.splitDepFactor` covers the set

As the exact layer's halves cover it (`splitDepFactor_union`): a point at factor value `αₖ ≤ 0` is
the left half's at `2αₖ + 1`, one at `αₖ ≥ 0` the right half's at `2αₖ - 1`, and
`getSubset_point_outer` carries it, with the error box, into that float half; `∓1/2` and `1/2`
read back as themselves. Outer, not exact.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `k` – factor index

## Hypotheses
* none

## Conclusion
* the set is covered by the two halves
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.splitDepFactor_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (k : Fin cPZ.p) :
    cPZ.construct ⊆
      (cPZ.splitDepFactor k).1.construct ∪ (cPZ.splitDepFactor k).2.construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, e, he, rfl⟩
  obtain ⟨a, β, ha, hβ, hs, hz⟩ := ConPolyZono.mem_nominalSet_iff.mp hz
  -- a half reaches the point at any factor vector its re-parametrization sends to `a`
  have key : ∀ (cen rad : 𝕋) (a' : Fin cPZ.p → ℝ), (∀ k, |a' k| ≤ 1) →
      Function.update a' k (toReal cen + toReal rad * a' k) = a →
        z + e ∈ (cPZ.getSubset k cen rad).construct := by
    intro cen rad a' ha' hupd
    obtain ⟨hs', hpt⟩ := ConPolyZono.getSubset_point_outer cPZ k cen rad a' ha' (hupd ▸ hs)
    obtain ⟨e', he', hsum⟩ := hpt e he
    refine ⟨fun i => toReal ((cPZ.getSubset k cen rad).c i)
        + (∑ l, toReal ((cPZ.getSubset k cen rad).G l i)
          * Real.PolyZonotope.monomial (cPZ.getSubset k cen rad).E a' l)
        + ∑ j, toReal ((cPZ.getSubset k cen rad).GI j i) * β j,
      ConPolyZono.mem_nominalSet_iff.mpr ⟨a', β, ha', hβ, hs', fun _ => rfl⟩, e', he', ?_⟩
    funext i
    have h := hsum i
    rw [hupd] at h
    show _ + e' i = z i + e i
    rw [hz i]
    have hGI : ∑ j, toReal ((cPZ.getSubset k cen rad).GI j i) * β j
        = ∑ j, toReal (cPZ.GI j i) * β j := rfl
    show toReal (cPZ.c i) + _ + _ + e' i = _
    linarith
  -- the half and the negated half, read back as reals
  have hc : toReal (neg (half (one : 𝕋))) = -(2 : ℝ)⁻¹ := by
    rw [toReal_neg, toReal_half, toReal_one]; norm_num
  have hr : toReal (half (one : 𝕋)) = (2 : ℝ)⁻¹ := by
    rw [toReal_half, toReal_one]; norm_num
  have hak := abs_le.mp (ha k)
  rcases le_total (a k) 0 with hneg | hpos
  · -- the left half, at `2αₖ + 1`
    refine Or.inl (key _ _ (Function.update a k (2 * a k + 1)) (fun l => ?_) ?_)
    · rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, abs_le]
        exact ⟨by linarith, by linarith⟩
      · rw [Function.update_of_ne hl]
        exact ha l
    · rw [Function.update_idem, Function.update_self, hc, hr]
      exact (congrArg (Function.update a k) (by ring)).trans (Function.update_eq_self k a)
  · -- the right half, at `2αₖ - 1`
    refine Or.inr (key _ _ (Function.update a k (2 * a k - 1)) (fun l => ?_) ?_)
    · rcases eq_or_ne l k with rfl | hl
      · rw [Function.update_self, abs_le]
        exact ⟨by linarith, by linarith⟩
      · rw [Function.update_of_ne hl]
        exact ha l
    · rw [Function.update_idem, Function.update_self, hr]
      exact (congrArg (Function.update a k) (by ring)).trans (Function.update_eq_self k a)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
