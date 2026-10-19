module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffImageSubsetImageOfConvex
public import CORALean.Global.Tensor

@[expose] public section

/-!
# A perturbed matrix image, inner-approximated without a smallness condition

`minkowskiDiff_image_subset_image_of_convex` at matrices: for any `Ē`, `E`, a convex compact `X` and
a nonempty bounded `B` covering `(Ē - E) X`, the image `Ē X` minus `B` lies inside `E X`. The image
`E X` is convex and compact as a linear image of one, which is all the cancellation asks.

Neither `Ē` invertible nor `‖Ē⁻¹ (E - Ē)‖ < 1` is needed, unlike the contraction route
(`minkowskiDiff_mulVec_image_subset_of_contracting`). For an interval matrix holding the true
`e^{AΔt}` and `X` a zonotope, `B` is any box covering `R |X|`, `R` the interval's radius.

## Inputs
* `Ē` – matrix
* `E` – matrix
* `X` – domain set
* `B` – error set

## Hypotheses
* `hXc` – `X` convex
* `hXk` – `X` compact
* `hBne` – `B` nonempty
* `hBb` – `B` bounded
* `hB` – `B` covers `Ē x - E x` on `X`

## Conclusion
* `Ē X ⊖ B` lies in `E X`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Ē X ⊖ B ⊆ E X` for any matrices `Ē`, `E`, a convex compact `X`, and a nonempty bounded `B`
covering `Ē x - E x` on `X`. -/
theorem minkowskiDiff_mulVec_image_subset_of_convex (Ē E : Mat ℝ m n) {X : Set (Vec ℝ n)}
    (hXc : Convex ℝ X) (hXk : IsCompact X) {B : Set (Vec ℝ m)} (hBne : B.Nonempty)
    (hBb : Bornology.IsBounded B) (hB : ∀ x ∈ X, Ē *ᵥ x - E *ᵥ x ∈ B) :
    minkowskiDiff ((Ē *ᵥ ·) '' X) B ⊆ (E *ᵥ ·) '' X :=
  minkowskiDiff_image_subset_image_of_convex (Ē *ᵥ ·) (E *ᵥ ·) hBne hBb
    (hXc.linear_image E.mulVecLin) (hXk.image E.mulVecLin.continuous_of_finiteDimensional).isClosed
    hB

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
