module

public import CORALean.ContSet.VPolytope.Real.Operations.CartProd
public import CORALean.ContSet.VPolytope.Real.Theorems.ConvexHull
public import CORALean.Global.AppendLinear
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

/-!
# `VPolytope.cartProd` is exact

[1, Eq. 28]: the hull of all stacked pairs of points is the product of the two hulls, stacked —
`convexHull_prod` carried through the linear map `appendLinear`.

## Inputs
* `P₁` – first polytope
* `P₂` – second polytope

## Hypotheses
* none

## Conclusion
* the result is exactly the product of the two sets

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral
      Operations in CORA 2024". In Proc. of the 11th International Workshop on Applied
      Verification of Continuous and Hybrid Systems (ARCH24), EPiC Series in Computing,
      vol. 103, pp. 163-181, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.cartProd_exact (P₁ : VPolytope (Vec ℝ n₁))
    (P₂ : VPolytope (Vec ℝ n₂)) : -- --- CONCL ---
    (P₁.cartProd P₂).construct =
      (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
        (P₁.construct ×ˢ P₂.construct) := by -- --- PROOF ---
  have hfun : (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) = appendLinear n₁ n₂ :=
    funext fun p => (appendLinear_apply p).symm
  -- the stacked points are the image of all pairs of points
  have hrange : Set.range (P₁.cartProd P₂).V =
      appendLinear n₁ n₂ '' (Set.range P₁.V ×ˢ Set.range P₂.V) := by
    ext z
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨(P₁.V (finProdFinEquiv.symm l).1, P₂.V (finProdFinEquiv.symm l).2),
        ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, appendLinear_apply _⟩
    · rintro ⟨⟨_, _⟩, ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩, rfl⟩
      refine ⟨finProdFinEquiv (i, j), ?_⟩
      rw [appendLinear_apply]
      simp [VPolytope.cartProd]
  rw [hfun, VPolytope.construct_eq_convexHull, hrange, ← LinearMap.image_convexHull,
    convexHull_prod, P₁.construct_eq_convexHull, P₂.construct_eq_convexHull]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
