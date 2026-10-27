module

public import CORALean.ContSet.ContSet.Operations.IntersectStripSeq

@[expose] public section

/-!
# The strips one at a time enclose the set's intersection with all of them

[1, Eq. 3]: each step is [1, Prop. 6] at one strip (`intersectStrip_outer` at a one-row `C`), and
a point in every strip is in strip `i`, so it survives each step in turn. For every gain, fixed or
computed from the set being met, and for every representation with `IntersectStrip`, float or
exact.

[2, Eq. 3] and [2, Eq. 4] in one, strip by strip.

## Inputs
* `C` – measurement matrix
* `φ` – strip lower offsets
* `y` – strip upper offsets
* `Λ` – gain matrix as a function of the set
* `Z` – initial set

## Hypotheses
* none

## Conclusion
* the set meeting all strips lies in the result

## References

* [1] [V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica,
      2013.](../../../../../references/2013/le-automatica-zonotopic-estimation.md)
* [2] [M. Althoff. "Guaranteed State Estimation in CORA 2021". 8th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH21),
      2021.](../../../../../references/2021/althoff-arch-state-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar IntersectStrip

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [IntersectStrip 𝕋 S] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.intersectStripSeq_outer (C : Mat 𝕋 p n) (φ y : Vec 𝕋 p) (Λ : S n → Mat 𝕋 n p)
    (Z : S n) : -- --- CONCL ---
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
