import CORALean.ContSet.ContSet.Operations.IntersectStripSeq
import Mathlib.Algebra.BigOperators.Fin

/-!
# The strips one at a time enclose the set's intersection with all of them

[1, Eq. 3]: each step is [1, Prop. 6] at one strip (`intersectStrip_outer` at a one-row `C`), and
a point in every strip is in strip `i`, so it survives each step in turn. For every gain, fixed or
computed from the set being met, and for every representation with `IntersectStrip`, float or
exact.

[2, Eq. 3] and [2, Eq. 4] in one, strip by strip.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.intersectStripSeq_outer (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : S n → Mat 𝕋 n p)
    (Z : S n) :
    construct Z ∩ {x | ∀ i, |(toRealMat C *ᵥ x - toRealVec y) i| ≤ toReal (φ i)} ⊆
      construct (ContSet.intersectStripSeq C φ y Λ Z) := by -- --- PROOF ---
  unfold ContSet.intersectStripSeq
  generalize List.finRange p = l
  induction l generalizing Z with
  | nil => exact Set.inter_subset_left
  | cons i t ih =>
    intro x hx
    refine ih _ ⟨?_, hx.2⟩
    -- strip `i` alone, as a one-row strip
    refine intersectStrip_outer _ _ _ _ Z ⟨hx.1, fun _ => ?_⟩
    simpa [Matrix.mulVec, dotProduct, toRealMat_apply, toRealVec_apply] using hx.2 i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
