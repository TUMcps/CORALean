module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxScale
public import CORALean.ContSet.Zonotope.Real.Theorems.MulGensInner

@[expose] public section

/-!
# `reduceUnderApproxScale` returns a subset

If the linear program's constraint holds, `G_o diag(λ) = G T` with `‖T‖∞ ≤ 1`, then
[1, Eq. (1)] gives `Ẑ ⊆ Z`. That `Z ⊆ Z_o` (Step 1) is not used: the template may be any zonotope.

## Inputs
* `Z` – zonotope
* `Zo` – zonotope supplying the generators
* `lam` – generator scalings
* `T` – recombination matrix

## Hypotheses
* `hG` – scaled generators recombine those of `Z`
* `hT` – row sums at most one

## Conclusion
* the scaled zonotope lies in `Z`

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-C]: the scaled template is inside `Z` when the program's constraint holds. -/
theorem Zonotope.reduceUnderApproxScale_inner (Z Zo : Zonotope α) (lam : Fin Zo.h → ℝ)
    (T : Mat ℝ Z.h Zo.h) (hG : ∀ j, lam j • Zo.G j = ∑ i, T i j • Z.G i)
    (hT : ∀ i, ∑ j, |T i j| ≤ 1) :
    (Z.reduceUnderApproxScale Zo lam).construct ⊆ Z.construct := by
  have e : Z.reduceUnderApproxScale Zo lam = Z.mulGens T := by
    simp only [Zonotope.reduceUnderApproxScale, Zonotope.mulGens, hG]
  rw [e]
  exact Zonotope.mulGens_inner Z T hT

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
