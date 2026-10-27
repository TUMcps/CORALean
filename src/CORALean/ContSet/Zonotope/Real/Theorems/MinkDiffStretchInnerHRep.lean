module

public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffStretchInner
public import CORALean.ContSet.Zonotope.Real.Theorems.HRepLinSubset

@[expose] public section

/-!
# [1, Thm. 4] at `Thm. 2`'s own directions

[1, Thm. 4] as printed takes its directions `C` from [1, Thm. 2]: the normalized cross
products of `n` generators of a minuend in `ℝⁿ⁺¹` whose generators span, both signs. At
those directions `minkDiffStretch_inner`'s premise `hCm` holds by `hRep_lin_subset`, so the
stretched minuend `(c⁽ᵐ⁾ - c⁽ˢ⁾, G⁽ᵐ⁾µ)` lies in `Z_m ⊖ Z_s` for every `µ ≥ 0` feasible for
`Âµ ≤ b̂` — the linear program's optimum `µ*` among them, its objective `ζᵀµ` choosing between
feasible points without bearing on the guarantee.

## Inputs
* `n` – dimension minus one
* `ι` – direction index type
* `Z₁` – minuend
* `Z₂` – subtrahend
* `C` – linear directions
* `μ` – stretch factors

## Hypotheses
* `hspan` – generators span the space
* `hC` – directions carry both signs of every normal
* `hμ0` – factors nonnegative
* `hμ` – factors satisfy the offset inequalities

## Conclusion
* the stretched minuend lies in the Minkowski difference

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 4], as printed: at `Thm. 2`'s directions, the stretched minuend at any feasible
`µ ≥ 0` under-approximates the Minkowski difference. -/
theorem Zonotope.minkDiffStretch_inner_hRep {n : ℕ} {ι : Type} (Z₁ Z₂ : Zonotope (Vec ℝ (n + 1)))
    (C : ι → (Vec ℝ (n + 1) →ₗ[ℝ] ℝ)) (hspan : Submodule.span ℝ (Set.range Z₁.G) = ⊤)
    (hC : ∀ S : Fin n → Fin Z₁.h, ∃ (i₁ i₂ : ι) (lam : ℝ), 0 < lam ∧
      (∀ y, C i₁ y = lam * (Z₁.facetNormal S ⬝ᵥ y)) ∧
      (∀ y, C i₂ y = -(lam * (Z₁.facetNormal S ⬝ᵥ y))))
    (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ υ, 0 ≤ μ υ)
    (hμ : ∀ i, ∑ υ, |C i (Z₁.G υ)| * μ υ
            ≤ (∑ υ, |C i (Z₁.G υ)|) - ∑ υ, |C i (Z₂.G υ)|) :
    (Z₁.minkDiffStretch Z₂ μ).construct
      ⊆ minkowskiDiff Z₁.construct Z₂.construct :=
  Z₁.minkDiffStretch_inner Z₂ C μ hμ0 (Z₁.hRep_lin_subset C hspan hC) hμ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
