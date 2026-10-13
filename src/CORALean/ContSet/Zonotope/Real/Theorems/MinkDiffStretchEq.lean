module

public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchInner
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffApplyLe

@[expose] public section

/-!
# [1, Prop. 6]: the stretched minuend is the difference where (22) holds exactly

[1, Prop. 6] reads its closed form off (22), `|Ĉ⁺Ĝ⁽ᵐ⁾| µ = Δd̂ - Δd̂_trans`. That
equation is the two inequalities [1, Thm. 4] and [1, Thm. 5] meet at: `≤` is
`minkDiffStretch_inner`'s constraint, `≥` is `minkDiffStretch_outer`'s at the
`b̃` of `minkowskiDiff_apply_le`, and together they pin the difference exactly.

Two side conditions the printed proposition does not carry. `µ ≥ 0` is needed:
at `Z₁` the unit square and `Z₂` twice it the difference is empty, while (22)
solves to `µ = (-1, -1)` and the closed form returns the unit square back. And
(22) must be solvable at all — "(22) has a unique solution" is what [1, (23)]
asserts for `n = 2`, where each generator owns one normal; nothing here proves
that, so the solved `µ` is an argument.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6]: at a nonnegative `µ` solving (22) exactly, the stretched
minuend *is* the Minkowski difference. -/
theorem Zonotope.minkDiffStretch_eq {ι : Type} (Z₁ Z₂ : Zonotope α)
    (C : ι → (α →ₗ[ℝ] ℝ)) (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ υ, 0 ≤ μ υ)
    (hCm : {y | ∀ i, C i (y - Z₁.c) ≤ ∑ υ, |C i (Z₁.G υ)|} ⊆ Z₁.construct)
    (hCd : {y | ∀ i, C i (y - (Z₁.minkDiffStretch Z₂ μ).c)
                ≤ ∑ υ, |C i ((Z₁.minkDiffStretch Z₂ μ).G υ)|}
            ⊆ (Z₁.minkDiffStretch Z₂ μ).construct)
    (hμ : ∀ i, ∑ υ, |C i (Z₁.G υ)| * μ υ
            = (∑ υ, |C i (Z₁.G υ)|) - ∑ υ, |C i (Z₂.G υ)|) :
    minkowskiDiff Z₁.construct Z₂.construct
      = (Z₁.minkDiffStretch Z₂ μ).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset ?_ ?_
  · -- `≥` in (22) is [1, Thm. 5] at the most conservative admissible `b̃`
    exact Z₁.minkDiffStretch_outer Z₂ C μ hμ0
      (fun i => (∑ υ, |C i (Z₁.G υ)|) - ∑ υ, |C i (Z₂.G υ)|)
      (fun i x hx => Z₁.minkowskiDiff_apply_le Z₂ (C i) hx) (fun i => (hμ i).ge) hCd
  · -- and `≤` in (22) is [1, Thm. 4]'s own constraint
    exact Z₁.minkDiffStretch_inner Z₂ C μ hμ0 hCm (fun i => (hμ i).le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
