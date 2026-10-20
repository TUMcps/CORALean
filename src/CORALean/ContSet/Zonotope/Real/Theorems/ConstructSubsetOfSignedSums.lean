module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConvexHullSignedSums
public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner

@[expose] public section

/-!
# A convex set holding the points `c + Z±(R)` holds the zonotopes

[1, Thm. 4]: with `P = ⋃ₗ (cₗ + Z±(Rₗ))` ([1, Eq. 41]), any convex `M` with `P ⊆ M`
contains every zonotope `cₗ ⊕ Z(Rₗ)`, hence their union. The paper states it for the MSPBs `Z⋆'ₗ`
(zonotopes with `2n` generators); it holds for any family of zonotopes.

## Inputs
* `Z` – family of zonotopes
* `M` – convex set

## Hypotheses
* `hM` – `M` convex
* `hP` – signed-sum points lie in `M`

## Conclusion
* the union of the zonotopes lies in `M`

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n L : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.iUnion_construct_subset_of_signedSums_subset (Z : Fin L → Zonotope (Vec ℝ n))
    {M : Set (Vec ℝ n)} (hM : Convex ℝ M)
    (hP : ⋃ l, (fun x => (Z l).c + x) '' Zonotope.signedSums (Z l).G ⊆ M) : -- --- CONCL ---
    ⋃ l, (Z l).construct ⊆ M := by -- --- PROOF ---
  refine Set.iUnion_subset fun l => ?_
  rw [Zonotope.construct_eq_convexHull_corner]
  refine convexHull_min ?_ hM
  rintro _ ⟨σ, rfl⟩
  exact hP (Set.mem_iUnion.mpr ⟨l, ⟨_, ⟨σ, rfl⟩, rfl⟩⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
