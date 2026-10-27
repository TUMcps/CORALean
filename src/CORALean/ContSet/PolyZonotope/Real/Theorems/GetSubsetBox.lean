module

public import CORALean.ContSet.PolyZonotope.Real.Operations.GetSubset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The unit box re-parametrized at one factor is a box again

`getSubset` replaces factor `k` by `cen + rad·αₖ`, so the unit box it is read
over becomes the box with `k`'s side at `cen ± rad` and every other side left
alone. A degenerate `rad = 0` pins the coordinate instead of shrinking it, which
is why the reverse inclusion divides by `rad` only where it may.

Its own file because both `getSubset_construct` and `getSubset_evalOn` name the
sub-box this way, and the second is [1, Thm. 1]'s initial inclusion.

## Inputs
* `p` – number of factors
* `k` – factor index
* `cen` – subinterval center
* `rad` – subinterval radius

## Hypotheses
* `hrad` – radius is nonnegative

## Conclusion
* the rescaled unit box is the box around the center in that factor

## References

* [1] [N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control,
      2020.](../../../../../../references/2020/kochdumper-hscc-utilizing-dependencies.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unit box, re-parametrized at factor `k`, is that box with `k`'s side
replaced by `cen ± rad`. -/
theorem PolyZonotope.getSubset_box {p : ℕ} (k : Fin p) {cen rad : ℝ}
    (hrad : 0 ≤ rad) : -- --- CONCL ---
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
