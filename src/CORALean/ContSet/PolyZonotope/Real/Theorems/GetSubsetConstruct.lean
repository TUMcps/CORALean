import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetSubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.SubsetAtUnitBox

/-!
# `getSubset` represents the subset a factor sub-box reaches

Naming that subset is [1, Thm. 1]'s subject; this represents it. The sub-box restricting
factor `k` to `cen ± rad` reaches *exactly* `getSubset`'s set — an equality, not
an enclosure, and at every degree: the re-parametrization is affine in the
factor, the monomials above degree one expand binomially, and that expansion is
an identity.

`hq` is `subsetAt_unitBox`'s hypothesis and where an enclosure would otherwise
creep in — `construct` widens by the independent block, which no factor names;
`restructure_q` is how a caller gets there, at `restructure_outer`'s price.
`hrad` is what makes `cen ± rad` an interval rather than an empty set.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The unit box, re-parametrized at factor `k`, is the box that box with `k`'s
side replaced by `cen ± rad`. -/
theorem PolyZonotope.aux_getSubset_box {p : ℕ} (k : Fin p) {cen rad : ℝ} (hrad : 0 ≤ rad) :
    (fun b : Fin p → ℝ => Function.update b k (cen + rad * b k)) '' {b | ∀ k', |b k'| ≤ 1}
      = {a | |a k - cen| ≤ rad ∧ ∀ k', k' ≠ k → |a k'| ≤ 1} := by -- --- PROOF ---
  ext a
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · -- a re-parametrized unit vector lands in the box, `|rad · bₖ| ≤ rad`
    rintro ⟨b, hb, rfl⟩
    refine ⟨?_, fun k' hk' => by rw [Function.update_of_ne hk']; exact hb k'⟩
    rw [Function.update_self, add_sub_cancel_left, abs_mul, abs_of_nonneg hrad]
    exact mul_le_of_le_one_right hrad (hb k)
  · -- and every point of the box is one, at `bₖ = (aₖ - cen) / rad`
    rintro ⟨h₁, h₂⟩
    refine ⟨Function.update a k (if rad = 0 then 0 else (a k - cen) / rad), fun k' => ?_, ?_⟩
    · rcases eq_or_ne k' k with rfl | hk'
      · rw [Function.update_self]
        rcases eq_or_ne rad 0 with hr | hr
        · rw [if_pos hr, abs_zero]
          exact zero_le_one
        · have hpos : 0 < rad := lt_of_le_of_ne hrad (Ne.symm hr)
          rw [if_neg hr, abs_div, abs_of_pos hpos]
          exact (div_le_one hpos).mpr h₁
      · rw [Function.update_of_ne hk']
        exact h₂ k' hk'
    · -- a zero radius pins the factor, and `h₁` then pins the coordinate to `cen`
      funext k'
      rcases eq_or_ne k' k with rfl | hk'
      · rw [Function.update_self, Function.update_self]
        rcases eq_or_ne rad 0 with hr | hr
        · rw [hr] at h₁
          rw [if_pos hr, mul_zero, add_zero]
          have := abs_nonpos_iff.mp h₁
          linarith
        · rw [if_neg hr]
          field_simp
          ring
      · rw [Function.update_of_ne hk', Function.update_of_ne hk']


-- =======================================  MAIN THEOREM  ======================================= --

/-- The subset the factor sub-box `αₖ ∈ cen ± rad` reaches is exactly what
`getSubset` constructs. -/
theorem PolyZonotope.getSubset_construct (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (hrad : 0 ≤ rad) (hq : pZ.q = 0) :
    pZ.subsetAt {a | |a k - cen| ≤ rad ∧ ∀ k', k' ≠ k → |a k'| ≤ 1}
      = (pZ.getSubset k cen rad).construct := by
  rw [← PolyZonotope.aux_getSubset_box k hrad, ← PolyZonotope.getSubset_subsetAt]
  exact PolyZonotope.subsetAt_unitBox _ hq

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
