module

public import CORALean.ContSet.Zonotope.Real.Operations.Venum
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner
public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetIffZonotopeNormLe
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# `venum` decides containment

`[1, Alg. 1]` is exact for a non-degenerate circumbody: `Z₁` is the convex hull of its
corners and `Z₂` is convex, so `Z₁ ⊆ Z₂` iff every corner lies in `Z₂`, which is
`‖v - c₂‖_{Z₂} ≤ 1` by `[1, Cor. 1]`.

## Inputs
* `Z₁` – zonotope tested
* `Z₂` – containing zonotope

## Hypotheses
* `hG` – generator map of `Z₂` surjective

## Conclusion
* the test is true iff `Z₁` lies in `Z₂`

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.venum_iff (Z₁ Z₂ : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z₂.genMap) : -- --- CONCL ---
    Z₁.venum Z₂ = true ↔ Z₁.construct ⊆ Z₂.construct := by -- --- PROOF ---
  have hball := (Z₂.zonotopeNorm_ball_eq hG).1
  -- the test is that every corner lies in `Z₂`
  have htest : Z₁.venum Z₂ = true ↔ ∀ σ, Z₁.corner σ ∈ Z₂.construct := by
    simp only [Zonotope.venum, Finset.mem_image, Finset.mem_univ, true_and, gt_iff_lt, not_lt,
      forall_exists_index, forall_apply_eq_imp_iff, ite_eq_left_iff, Bool.false_eq_true,
      imp_false, not_not]
    rw [← hball]
    rfl
  rw [htest, Z₁.construct_eq_convexHull_corner]
  constructor
  · intro h
    exact convexHull_min (by rintro _ ⟨σ, rfl⟩; exact h σ) Z₂.convex_construct
  · intro h σ
    exact h (subset_convexHull ℝ _ ⟨σ, rfl⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
