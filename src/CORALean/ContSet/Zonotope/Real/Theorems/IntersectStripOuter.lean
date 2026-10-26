module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectStrip
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# `Zonotope.intersectStrip` encloses the zonotope's intersection with the strips

For every weight matrix `Λ`: [4, Prop. 1] as printed, `p ⊕ H Bʳ` met with `|C x - d| ≤ φ` lies in
`p̂(Λ) ⊕ Ĥ(Λ) Bʳ⁺ᵐ`, `p̂(Λ) = p + Λ (d - C p)`, `Ĥ(Λ) = [(I - Λ C) H, Λ diag(φ)]`; [4, Eq. 10] at
the prediction, and [2, Eq. 3] with [2, Eq. 4], the strips met all at once with the predicted set.
At one strip and a gain column `λ` this is [1, Prop. 6], that is [3, Property 2]. A point
`x = c + G β` with `|C x - y| ≤ φ` is `(I - Λ C) x + Λ (C x)`, and `C x = y + φ ⊙ γ` with
`γ ∈ [-1, 1]^p`, so the coefficients `β` on the old generators and `γ` on the strip ones reach it.
Outer only: the result in general holds more than the intersection, so no equality is claimed.

## Inputs
* `C` – output matrix
* `φ` – strip radii
* `y` – measurement
* `Λ` – weight matrix
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the intersection with the strip lies in the result

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21), 2021.
* [3] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 2005.
* [4] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotope-based set-membership
      estimation for multi-output uncertain systems". 2013 IEEE International Symposium on
      Intelligent Control (ISIC), 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem Zonotope.aux_mulVec_sum {m q : ℕ} {ι : Type} [Fintype ι] (M : Mat ℝ m q)
    (f : ι → Vec ℝ q) : M *ᵥ ∑ a, f a = ∑ a, M *ᵥ f a :=
  map_sum (Matrix.mulVecLin M) f Finset.univ


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectStrip_outer (C : Mat ℝ p n) (φ y : Vec ℝ p) (Λ : Mat ℝ n p)
    (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    Z.construct ∩ {x | ∀ i, |(C *ᵥ x - y) i| ≤ φ i} ⊆
      (Z.intersectStrip C φ y Λ).construct := by -- --- PROOF ---
  rintro x ⟨⟨β, hβ, rfl⟩, hs⟩
  -- the strip coefficients: `φ_i γ_i = (C x - y)_i`
  set x := Z.c + ∑ j, β j • Z.G j with hx
  let γ : Fin p → ℝ := fun i => (C *ᵥ x - y) i / φ i
  have hγ : ∀ i, |γ i| ≤ 1 := by
    intro i
    have hi := hs i
    have hφ : 0 ≤ φ i := le_trans (abs_nonneg _) hi
    by_cases h0 : φ i = 0
    · simp [γ, h0]
    · have hpos : 0 < φ i := lt_of_le_of_ne hφ (Ne.symm h0)
      simp only [γ, abs_div, abs_of_pos hpos]
      exact (div_le_one hpos).mpr hi
  -- they reproduce the strip residual
  have hγφ : ∀ i, γ i * φ i = (C *ᵥ x - y) i := by
    intro i
    have hi := hs i
    have hφ : 0 ≤ φ i := le_trans (abs_nonneg _) hi
    by_cases h0 : φ i = 0
    · have : (C *ᵥ x - y) i = 0 := abs_nonpos_iff.mp (h0 ▸ hi)
      simp [γ, h0, this]
    · exact div_mul_cancel₀ _ h0
  refine ⟨Fin.append β γ, ?_, ?_⟩
  · -- the coefficients stay in `[-1, 1]`
    intro j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) j
    · simpa using hβ a
    · simpa using hγ a
  · -- the sum splits into the old generators and the strip ones
    show x = Z.c + Λ *ᵥ (y - C *ᵥ Z.c) + ∑ j : Fin (Z.h + p), Fin.append β γ j •
      Fin.append (fun j => (1 - Λ * C) *ᵥ Z.G j) (fun i => Λ *ᵥ Pi.single i (φ i)) j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h1 : ∑ a : Fin Z.h, β a • ((1 - Λ * C) *ᵥ Z.G a) =
        (1 - Λ * C) *ᵥ (x - Z.c) := by
      rw [hx, add_sub_cancel_left, Zonotope.aux_mulVec_sum]
      exact Finset.sum_congr rfl fun a _ => (Matrix.mulVec_smul _ _ _).symm
    have h2 : ∑ a : Fin p, γ a • (Λ *ᵥ Pi.single a (φ a)) =
        Λ *ᵥ (C *ᵥ x - y) := by
      have hsum : ∑ a : Fin p, γ a • (Pi.single a (φ a) : Vec ℝ p) = C *ᵥ x - y := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, ← hγφ k]
      rw [← hsum, Zonotope.aux_mulVec_sum]
      exact Finset.sum_congr rfl fun a _ => (Matrix.mulVec_smul _ _ _).symm
    rw [h1, h2]
    -- `x = c + Λ (y - C c) + (I - Λ C)(x - c) + Λ (C x - y)`
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
