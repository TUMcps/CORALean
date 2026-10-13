import CORALean.ContSet.Zonotope.Real.Theorems.HRepEq
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffApplyLe

/-!
# [1, Thm. 3]: the Minkowski difference's own halfspace representation

`Z_m ⊖ Z_s = {x | C(x − (c⁽ᵐ⁾ − c⁽ˢ⁾)) ≤ Δd − Δd_trans}`, the same `C` as [1,
Thm. 2] at the minuend `Z_m` alone, `Δd` its own reach and `Δd_trans` the
subtrahend's — the printed `±` pair read, as at `Thm. 2` and `Lemma 2`, as one
`|·|` row.

`hspan` is `Thm. 2`'s own hypothesis at `Z_m`, needed to read off `hRep_eq`
there; `Z_s` carries none, and needs none. Enclosing: `minkowskiDiff_apply_le`
at `Thm. 2`'s own normal and its negation. Exhausting: any point of `Z_s`
displaces `Z_m`'s halfspaces by at most its own support value in that
direction, so `hRep_eq` at the sum keeps `x` inside.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `⬝ᵥ` as a bilinear pairing, so the enclosing half can be read off both a
direction and its negation through `minkowskiDiff_apply_le`. -/
def aux_dotBilin {n : ℕ} : Vec ℝ (n + 1) →ₗ[ℝ] Vec ℝ (n + 1) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v : Vec ℝ (n + 1) => u ⬝ᵥ v)
    (fun a b c => add_dotProduct a b c) (fun c a b => smul_dotProduct c a b)
    (fun a b c => dotProduct_add a b c) (fun c a b => dotProduct_smul c a b)


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3]: the Minkowski difference at `Z_m`'s own halfspaces, `Δd`
lowered by `Z_s`'s own support value `Δd_trans` in each direction. -/
theorem Zonotope.minkowskiDiff_hRep_eq {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 1)))
    (hspan : Submodule.span ℝ (Set.range Zm.G) = ⊤) :
    minkowskiDiff Zm.construct Zs.construct = {x | ∀ S : Fin n → Fin Zm.h,
      |Zm.facetNormal S ⬝ᵥ (x - (Zm.c - Zs.c))| ≤
        (∑ υ, |Zm.facetNormal S ⬝ᵥ Zm.G υ|) -
          ∑ υ, |Zm.facetNormal S ⬝ᵥ Zs.G υ|} := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx => ?_)
  · -- enclosing: read `Δd - Δd_trans` off both `p` and `-p`
    intro S
    set p := Zm.facetNormal S with hp
    have hpos := Zm.minkowskiDiff_apply_le Zs (aux_dotBilin p) hx
    have hneg := Zm.minkowskiDiff_apply_le Zs (aux_dotBilin (-p)) hx
    simp only [aux_dotBilin, LinearMap.mk₂_apply, neg_dotProduct, abs_neg] at hpos hneg
    exact abs_le.mpr ⟨by linarith [hneg], hpos⟩
  · -- exhausting: any point of `Z_s` displaces `Z_m`'s halfspaces by at most its own reach
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    rw [Zm.hRep_eq hspan]
    intro S
    set p := Zm.facetNormal S with hp
    have hxS := hx S
    have hb : |p ⬝ᵥ (Zs.c + ∑ υ, γ υ • Zs.G υ - Zs.c)| ≤ ∑ υ, |p ⬝ᵥ Zs.G υ| := by
      have hsub : Zs.c + ∑ υ, γ υ • Zs.G υ - Zs.c = ∑ υ, γ υ • Zs.G υ := by abel
      rw [hsub, dotProduct_sum]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun υ _ => ?_)
      rw [dotProduct_smul, smul_eq_mul, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hγ υ)
    have hsplit : x + (Zs.c + ∑ υ, γ υ • Zs.G υ) - Zm.c
        = (x - (Zm.c - Zs.c)) + (Zs.c + ∑ υ, γ υ • Zs.G υ - Zs.c) := by abel
    rw [hsplit, dotProduct_add]
    calc |p ⬝ᵥ (x - (Zm.c - Zs.c)) + p ⬝ᵥ (Zs.c + ∑ υ, γ υ • Zs.G υ - Zs.c)|
        ≤ |p ⬝ᵥ (x - (Zm.c - Zs.c))| + |p ⬝ᵥ (Zs.c + ∑ υ, γ υ • Zs.G υ - Zs.c)| := abs_add_le _ _
      _ ≤ ((∑ υ, |p ⬝ᵥ Zm.G υ|) - ∑ υ, |p ⬝ᵥ Zs.G υ|) + ∑ υ, |p ⬝ᵥ Zs.G υ| := add_le_add hxS hb
      _ = ∑ υ, |p ⬝ᵥ Zm.G υ| := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
