module

public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedInner
public import CORALean.ContSet.Zonotope.Real.Theorems.MinkDiffAlignedOuter

@[expose] public section

/-!
# `Zonotope.minkDiffAligned` computes the Minkowski difference exactly

[1, Prop. 5] as it is printed: at aligned generators the difference is *computed*,
`c⁽ᵐ⁾ - c⁽ˢ⁾` and `G⁽ᵐ⁾ - G⁽ˢ⁾` and nothing else. Both inclusions are available —
`minkDiffAligned_inner` splits a membership into one of each operand, `minkDiffAligned_outer`
collapses [1, Thm. 1]'s recursion onto the same closed form — so this is their antisymmetry. The
scaling `μ` is the alignment witness [1, Def. 3] asks to exist, explicit because the closed form
is about a particular pairing of the two generator families, which `hh` alone does not fix.
`0 ≤ μᵢ ≤ 1` is not in [1, Prop. 5], and is no convenience: outside it the equality fails in both
directions (`minkDiffAligned_not_inner`). [2, Prop. 3] is the same for [2, Def. 1]'s zonotopes.

## Inputs
* `Z₁` – minuend
* `Z₂` – subtrahend
* `μ` – generator scalings

## Hypotheses
* `hh` – equal generator counts
* `hμ0` – scalings nonnegative
* `hμ1` – scalings at most one
* `hG` – generators of `Z₂` scale those of `Z₁`

## Conclusion
* the closed form equals the Minkowski difference

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
* [2] [L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters,
      2022.](../../../../../../references/2022/yang-lcss-zonotopic-underapproximation.md)
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   04-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 5]: at generators aligned by a scaling in `[0, 1]`, the closed form
`(c⁽ᵐ⁾ - c⁽ˢ⁾, G⁽ᵐ⁾ - G⁽ˢ⁾)` *is* the Minkowski difference. -/
theorem Zonotope.minkDiffAligned_exact (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h)
    (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∀ i, μ i ≤ 1)
    (hG : ∀ i, Z₂.G (Fin.cast hh i) = μ i • Z₁.G i) :
    (Z₁.minkDiffAligned Z₂ hh).construct = minkowskiDiff Z₁.construct Z₂.construct :=
  Set.Subset.antisymm (Z₁.minkDiffAligned_inner Z₂ hh μ hμ0 hμ1 hG)
    (Z₁.minkDiffAligned_outer Z₂ hh μ hμ0 hμ1 hG)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
