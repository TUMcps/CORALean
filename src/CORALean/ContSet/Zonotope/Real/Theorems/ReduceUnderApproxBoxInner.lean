module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxBox
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.SplitKeptAddSplitDroppedSubset

@[expose] public section

/-!
# `reduceUnderApproxBox` returns a subset

For orthogonal `U`: if the box lies in the rotated part, `B ⊆ Z_br = Uᵀ Z_b` (Step 3), then
`U B ⊆ U Uᵀ Z_b = Z_b` (Step 4), and `Ẑ = Z_a ⊕ U B ⊆ Z_a ⊕ Z_b = Z`. The hypothesis is what the
program in Step 3 enforces through (1); `U` need not come from the singular value decomposition.

## Inputs
* `Z` – zonotope
* `o` – target order
* `U` – orthogonal basis
* `γ` – box radii

## Hypotheses
* `hlt` – reduction needed
* `hU` – `U` orthogonal
* `hB` – box lies in the rotated dropped part

## Conclusion
* the under-approximation lies in `Z`

## References

* [1] L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the
      Order Reduction of Zonotopes". IEEE Control Systems Letters, 9:1730-1735, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real
open scoped CORALean
open Pointwise
variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-B]: a box inside `Uᵀ Z_b`, for orthogonal `U`, gives `Ẑ ⊆ Z`. -/
theorem Zonotope.reduceUnderApproxBox_inner (Z : Zonotope (Vec ℝ n)) (o : ℕ)
    (hlt : o * n < Z.h) (U : Mat ℝ n n) (γ : Vec ℝ n) (hU : U * U.transpose = 1)
    (hB : (⟨n, 0, Matrix.diagonal γ⟩ : Zonotope (Vec ℝ n)).construct ⊆
      (Zonotope.mtimes U.transpose (Z.splitDropped (Z.girardSplit o hlt))).construct)
    : -- --- CONCL ---
    (Z.reduceUnderApproxBox o hlt U γ).construct ⊆ Z.construct := by -- --- PROOF ---
  -- `U B ⊆ Z_b`: a point of `B` is `Uᵀ z` for `z ∈ Z_b`, and `U Uᵀ z = z`
  have hUB : (Zonotope.mtimes U ⟨n, 0, Matrix.diagonal γ⟩).construct ⊆
      (Z.splitDropped (Z.girardSplit o hlt)).construct := by
    rw [← Zonotope.mtimes_exact]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hB hx
    rw [← Zonotope.mtimes_exact] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    rw [← hzx]
    show Matrix.mulVec U (Matrix.mulVec U.transpose z) ∈ _
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    exact hz
  unfold Zonotope.reduceUnderApproxBox
  simp only []
  rw [← Zonotope.plus_exact]
  exact (Set.add_subset_add_left hUB).trans
    (Zonotope.splitKept_add_splitDropped_subset Z _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
