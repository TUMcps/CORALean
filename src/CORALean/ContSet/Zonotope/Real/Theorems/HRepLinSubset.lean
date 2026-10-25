module

public import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq

@[expose] public section

/-!
# [1, Thm. 2] in the shape [1, Thm. 4] and [1, Thm. 5] ask for it

Those two carry `hCm`/`hCd`, the premise that their directions `C` *describe* the minuend rather
than only enclose it, as an explicit hypothesis. This discharges it: any family of linear forms
carrying both signs of every cross-product normal — `C` of [1, Thm. 2], `2·C(p, n-1)` rows — cuts
the zonotope out exactly. A positive factor `lam` is allowed per normal because a halfspace is
unchanged by scaling its normal and its offset together, which is what the printed `C`'s `1/‖nX‖₂`
does, and what a stretched minuend's own normals differ by.

## Inputs
* `n` – dimension minus one
* `ι` – index type
* `Z` – zonotope
* `C` – family of linear directions

## Hypotheses
* `hspan` – generators span the space
* `hC` – directions carry both signs of every normal

## Conclusion
* the described set lies in `Z`

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2] as `hCm`/`hCd` want it: directions carrying both signs of every
cross-product normal describe the zonotope. -/
theorem Zonotope.hRep_lin_subset {n : ℕ} {ι : Type} (Z : Zonotope (Vec ℝ (n + 1)))
    (C : ι → (Vec ℝ (n + 1) →ₗ[ℝ] ℝ)) (hspan : Submodule.span ℝ (Set.range Z.G) = ⊤)
    (hC : ∀ S : Fin n → Fin Z.h, ∃ (i₁ i₂ : ι) (lam : ℝ), 0 < lam ∧
      (∀ y, C i₁ y = lam * (Z.facetNormal S ⬝ᵥ y)) ∧
      (∀ y, C i₂ y = -(lam * (Z.facetNormal S ⬝ᵥ y)))) : -- --- CONCL ---
    {y | ∀ i, C i (y - Z.c) ≤ ∑ υ, |C i (Z.G υ)|} ⊆ Z.construct := by -- --- PROOF ---
  intro y hy
  rw [Z.hRep_eq hspan]
  intro S
  obtain ⟨i₁, i₂, lam, hlam, hp, hm⟩ := hC S
  -- the scaling cancels: it multiplies both sides of the row by `lam`
  have hsp : ∑ υ, |C i₁ (Z.G υ)| = lam * ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun υ _ => by
      rw [hp, abs_mul, abs_of_pos hlam]
  have hsm : ∑ υ, |C i₂ (Z.G υ)| = lam * ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun υ _ => by
      rw [hm, abs_neg, abs_mul, abs_of_pos hlam]
  have hpos := hy i₁
  have hneg := hy i₂
  rw [hp, hsp] at hpos
  rw [hm, hsm] at hneg
  rw [abs_le]
  refine ⟨?_, le_of_mul_le_mul_left hpos hlam⟩
  have h₂ : lam * -(Z.facetNormal S ⬝ᵥ (y - Z.c))
      ≤ lam * ∑ υ, |Z.facetNormal S ⬝ᵥ Z.G υ| := by rw [mul_neg]; exact hneg
  linarith [le_of_mul_le_mul_left h₂ hlam]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
