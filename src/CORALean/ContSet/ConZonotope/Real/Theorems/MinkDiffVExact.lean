module

public import CORALean.ContSet.ConZonotope.Real.Operations.MinkDiffV
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq
public import CORALean.ContSet.VPolytope.Real.Theorems.MinkowskiDiffEqIInter
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.ShiftMemIff
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact

@[expose] public section

/-!
# `minkDiffV` is exactly the Minkowski difference

[1, Prop. 6]: `minkDiffV` denotes `Z ⊖ ⟨v⟩_V` on the nose, no enclosure anywhere. Two steps:
`minkowskiDiff_eq_iInter` reduces the Minkowski difference by the vertex polytope to the
intersection of the translated zonotopes `Z − v i`, and `construct_foldl_intersection_eq` reads
the fold that computes `minkDiffV` as exactly that intersection.

Unlike `MinkDiff.minkDiff_inner`'s obligation, an under-approximation for a total operation, this
holds with no enclosure loss at all — [1]'s two-line derivation via `⋂ᵢ (Z − vᵢ)` costs nothing to
carry through here.

## Inputs
* `k` – number of extra vertices
* `Z` – zonotope
* `v` – vertex list of the polytope

## Hypotheses
* none

## Conclusion
* the result is exactly the Minkowski difference

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6]: the constrained zonotope `minkDiffV Z v` denotes exactly `Z ⊖ ⟨v⟩_V`. -/
theorem ConZonotope.minkDiffV_exact {k : ℕ} (Z : Zonotope (Vec ℝ n))
    (v : Fin (k + 1) → Vec ℝ n) : -- --- CONCL ---
    (ConZonotope.minkDiffV Z v).construct = minkowskiDiff Z.construct
      (⟨k + 1, v⟩ : VPolytope (Vec ℝ n)).construct := by -- --- PROOF ---
  rw [VPolytope.minkowskiDiff_eq_iInter Z.convex_construct]
  unfold ConZonotope.minkDiffV
  rw [ConZonotope.construct_foldl_intersection_eq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, ← Zonotope.conZonotope_exact,
    Zonotope.mem_shift_iff, Set.mem_setOf_eq, Fin.forall_fin_succ]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
