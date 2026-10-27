module

public import CORALean.ContSet.Zonotope.Real.Operations.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.BilinOuter

@[expose] public section

/-!
# A matrix zonotope's product over-approximates every matrix it denotes

The result is [1, Eq. 10] with a vector zonotope as the second factor.

`bilin_outer` at `Matrix.mulVecBilin ℝ ℝ`, whose application is `*ᵥ` by `rfl`
(`Matrix.mulVecBilin_apply`) — so the two unions of images are the same set,
matched pointwise rather than rewritten.

## Inputs
* `M` – matrix zonotope
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* all products lie in the result

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesMatZonotope_outer (M : Zonotope (Mat ℝ m n)) (Z : Zonotope (Vec ℝ n)) :
    (⋃ A ∈ M.construct, (A *ᵥ ·) '' Z.construct)
      ⊆ (Zonotope.mtimesMatZonotope M Z).construct := by
  -- `h` first, with no expected type: against the goal directly its module instances time out
  have h := Zonotope.bilin_outer (Matrix.mulVecBilin ℝ ℝ) M Z
  simp only [← Matrix.mulVecBilin_apply ℝ ℝ]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
