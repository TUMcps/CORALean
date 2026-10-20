module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MinkDiffConstruct
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# `ConPolyZono.minkDiff` is exact for a convex minuend

The corner points `x + c + Σ ±gⱼ` all lie in `P`, and `x + c + Σ βⱼ gⱼ` for `|β| ≤ 1` is their
convex combination (the cube is the convex hull of its corners, and `β ↦ x + c + Σ βⱼ gⱼ` is
affine), so `x + Z ⊆ P` when `P` is convex. With `minkDiff_outer` the result is `P ⊖ Z`. Without
convexity this is false: `minkDiff_not_inner`.

## Inputs
* `cPZ₁` – minuend
* `Z` – zonotope subtrahend

## Hypotheses
* `hP` – minuend is convex

## Conclusion
* the result is contained in the Minkowski difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.minkDiff_inner_of_convex (cPZ₁ : ConPolyZono (Vec ℝ n))
    (Z : Zonotope (Vec ℝ n)) (hP : Convex ℝ cPZ₁.construct) : -- --- CONCL ---
    (cPZ₁.minkDiff Z).construct ⊆
      {x | ∀ z ∈ Z.construct, x + z ∈ cPZ₁.construct} := by -- --- PROOF ---
  -- the affine map of coefficients to the shifted points
  rw [ConPolyZono.minkDiff_construct]
  intro x hx z ⟨β, hβ, hz⟩
  let L : (Fin Z.h → ℝ) →ₗ[ℝ] Vec ℝ n :=
    ∑ j, (LinearMap.proj j : (Fin Z.h → ℝ) →ₗ[ℝ] ℝ).smulRight (Z.G j)
  let φ : (Fin Z.h → ℝ) →ᵃ[ℝ] Vec ℝ n :=
    AffineMap.const ℝ (Fin Z.h → ℝ) (x + Z.c) + L.toAffineMap
  have hφ : ∀ γ, φ γ = x + (Z.c + ∑ j, γ j • Z.G j) := fun γ => by
    simp [φ, L, add_assoc]
  -- the corners of the cube are mapped into `P`
  have hcorner :
      φ '' (Set.pi (Set.univ : Set (Fin Z.h)) fun _ => ({-1, 1} : Set ℝ)) ⊆ cPZ₁.construct := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hφ]
    have := hx (fun j => decide (γ j = 1))
    convert this using 3
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : γ j = -1 ∨ γ j = 1 := by simpa using hγ j (Set.mem_univ j)
    rcases hj with h | h
    · simp [h]; norm_num
    · simp [h]
  -- the cube is their convex hull, and `φ` is affine
  have hcube :
      (Set.pi (Set.univ : Set (Fin Z.h)) fun _ => Set.Icc (-1 : ℝ) 1) ⊆ φ ⁻¹' cPZ₁.construct := by
    have h1 : convexHull ℝ (Set.pi (Set.univ : Set (Fin Z.h)) fun _ => ({-1, 1} : Set ℝ))
        = Set.pi (Set.univ : Set (Fin Z.h)) fun _ => Set.Icc (-1 : ℝ) 1 := by
      rw [convexHull_pi]
      simp only [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← h1]
    intro γ hγ
    have h2 : φ γ ∈ φ '' convexHull ℝ
        (Set.pi (Set.univ : Set (Fin Z.h)) fun _ => ({-1, 1} : Set ℝ)) := ⟨γ, hγ, rfl⟩
    rw [AffineMap.image_convexHull] at h2
    exact (hP.convexHull_subset_iff.mpr hcorner) h2
  have := hcube (fun j _ => abs_le.mp (hβ j))
  rw [Set.mem_preimage, hφ] at this
  rw [hz, ← add_assoc] at *
  simpa [add_assoc] using this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
