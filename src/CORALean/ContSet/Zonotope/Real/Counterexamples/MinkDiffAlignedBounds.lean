module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.Aligned
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The inner bound of the Minkowski difference fails at (max-in) over `W`'s halfspaces

[1, Prop. 4] sandwiches `Z ⊖ EW` between the differences with the outer and the inner aligned
zonotopes, `Z ⊖ Z̄ ⊆ Z ⊖ EW ⊆ Z ⊖ Z̲`. Its right inclusion needs `Z̲ ⊆ EW`, which [1, Prop. 2]
claims for the maximizer of (max-in) built from `W`'s own halfspaces and which fails there
(`aligned_subset_of_maxIn_counterexample`). In one dimension with `W = Z = [-1, 1]` and
`E = ½` the maximizer is `Z̲ = [-1, 1]`: `Z ⊖ Z̲ = {0}`, while `Z ⊖ EW = [-½, ½]`.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 4] as printed: with (max-in) over `W`'s halfspaces, `Z ⊖ EW` is not inside
`Z ⊖ Z̲`. -/
theorem Zonotope.minkDiffAligned_bounds_counterexample : -- --- STMT ---
    ∃ (Z : Zonotope (Vec ℝ 1)) (H : Mat ℝ 2 1) (h : Vec ℝ 2) (E : Mat ℝ 1 1) (c : Vec ℝ 1)
      (a : Fin Z.h → ℝ),
      (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ (∀ l, (H *ᵥ c) l + ∑ i, |(H *ᵥ Z.G i) l| * a i ≤ h l) ∧
      (∀ (c' : Vec ℝ 1) (a' : Fin Z.h → ℝ), (∀ i, 0 ≤ a' i ∧ a' i ≤ 1) →
        (∀ l, (H *ᵥ c') l + ∑ i, |(H *ᵥ Z.G i) l| * a' i ≤ h l) →
        ∑ i, ‖Z.G i‖ * Real.log (a' i) ≤ ∑ i, ‖Z.G i‖ * Real.log (a i)) ∧
      ¬ minkowskiDiff Z.construct ((E *ᵥ ·) '' {w | ∀ l, (H *ᵥ w) l ≤ h l})
          ⊆ minkowskiDiff Z.construct (Z.aligned c a).construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ _ => 1⟩, !![1; -1], ![1, 1], !![1 / 2], 0, fun _ => 1,
    fun _ => ⟨zero_le_one, le_rfl⟩, ?_, ?_, ?_⟩
  · intro l
    fin_cases l <;> simp [Matrix.mulVec, dotProduct]
  · intro c' a' ha' _
    simp only [Real.log_one, mul_zero, Finset.sum_const_zero]
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (Real.log_nonpos (ha' i).1 (ha' i).2)
  · intro hsub
    -- `½ ∈ Z ⊖ EW`: the points of `EW` are at most `½` in every coordinate
    have hhalf : (fun _ => 1 / 2 : Vec ℝ 1) ∈ minkowskiDiff
        (⟨1, 0, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)).construct
        ((!![1 / 2] *ᵥ ·) ''
          {w : Vec ℝ 1 | ∀ l, ((!![1; -1] : Mat ℝ 2 1) *ᵥ w) l ≤ ![1, 1] l}) := by
      rintro _ ⟨w, hw, rfl⟩
      have h0 := hw 0
      have h1 := hw 1
      simp [Matrix.mulVec, dotProduct] at h0 h1
      have a1 : (w 0 : ℝ) ≤ 1 := h0
      have a2 : -(w 0 : ℝ) ≤ 1 := h1
      have hb : |(1 / 2 + (w 0 : ℝ) / 2)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      refine ⟨fun _ => (1 / 2 + (w 0 : ℝ) / 2), fun _ => hb, ?_⟩
      funext i
      fin_cases i
      simp [dotProduct]
      ring
    have hgood := hsub hhalf
    -- but `½ + 1 ∉ Z`, while `1 ∈ Z̲`
    have hy : ((fun _ => 1 : Vec ℝ 1)) ∈ (Zonotope.aligned
        (⟨1, 0, fun _ _ => 1⟩ : Zonotope (Vec ℝ 1)) 0 (fun _ => (1 : ℝ))).construct := by
      refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
      funext i
      simp [Zonotope.aligned]
    obtain ⟨β, hβ, hx⟩ := hgood _ hy
    have h0 := congrFun hx 0
    simp at h0
    have := abs_le.mp (hβ 0)
    linarith [this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
