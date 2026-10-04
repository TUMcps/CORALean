import CORALean.ContSet.Zonotope.Real.Operations.IntersectStripSeq
import CORALean.ContSet.Zonotope.Real.Theorems.IntersectStripOuter

/-!
# `Zonotope.intersectStripSeq` encloses the zonotope's intersection with the strips

[1, Eq. 3]: each step is [1, Prop. 6] at one strip (`intersectStrip_outer` at a one-row `C`), and
a point in every strip is in strip `i`, so it survives each step in turn. For every gain, fixed or
computed from the zonotope being met.

[2, Eq. 3] and [2, Eq. 4] in one, strip by strip.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectStripSeq_outer (C : Mat ℝ p n) (φ y : Vec ℝ p)
    (Λ : Zonotope (Vec ℝ n) → Mat ℝ n p) (Z : Zonotope (Vec ℝ n)) :
    Z.construct ∩ {x | ∀ i, |(C *ᵥ x - y) i| ≤ φ i} ⊆
      (Z.intersectStripSeq C φ y Λ).construct := by -- --- PROOF ---
  unfold Zonotope.intersectStripSeq
  generalize List.finRange p = l
  induction l generalizing Z with
  | nil => exact Set.inter_subset_left
  | cons i t ih =>
    intro x hx
    refine ih _ ⟨?_, hx.2⟩
    -- strip `i` alone, as a one-row strip
    refine Zonotope.intersectStrip_outer _ _ _ _ Z ⟨hx.1, fun _ => ?_⟩
    simpa [Matrix.mulVec, dotProduct] using hx.2 i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
