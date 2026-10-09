import Mathlib.Topology.Algebra.Module.FiniteDimension
import CORALean.ContSet.ContSet.Theorems.MinkowskiDiffImageSubsetImageOfConvex
import CORALean.Global.Tensor

/-!
# A perturbed matrix image, inner-approximated without a smallness condition

`minkowskiDiff_image_subset_image_of_convex` at matrices: for any `Ē`, `E`, a
convex compact `X` and a nonempty bounded `B` covering `(Ē - E) X`, the image
`Ē X` minus `B` lies inside `E X`. The image `E X` is convex and compact as a
linear image of one, which is all the cancellation asks.

Neither `Ē` invertible nor `‖Ē⁻¹ (E - Ē)‖ < 1` is needed here, unlike the
contraction route (`minkowskiDiff_mulVec_image_subset_of_contracting`), which
pays for a closed `X` that need not be convex. For an interval matrix holding
the true `e^{AΔt}` and `X` a zonotope, this is the statement to use: `B` is any
box covering `R |X|`, `R` the interval's radius.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


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
