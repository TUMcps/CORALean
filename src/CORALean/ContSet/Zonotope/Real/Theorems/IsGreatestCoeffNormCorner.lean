module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner
public import CORALean.Global.CoeffNorm
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic.Module
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# A zonotope's distance from an ellipsotope is attained at a corner

`[1, Sec. III]`: for a zonotope inbody `Ẑ`, "according to the Bauer maximum principle, the
maximum of (6) is attained at one of the vertices", `α ∈ {-1, +1}^m`. The circumbody's norm
`‖·‖_{E_q(H)}` is convex, `Ẑ` is the convex hull of its sign corners, and a convex function
on a convex hull is beaten by one of the points it is the hull of. Any norm on the
circumbody's coefficients; `H` onto.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isGreatest_coeffNorm_corner (Z : Zonotope (Vec ℝ n)) (H : E →ₗ[ℝ] Vec ℝ n)
    (hH : Function.Surjective H) (d : Vec ℝ n) : -- --- STMT ---
    IsGreatest ((fun p => coeffNorm H (p - d)) '' Z.construct)
      (Finset.univ.sup' Finset.univ_nonempty fun σ =>
        coeffNorm H (Z.corner σ - d)) := by -- --- PROOF ---
  have hhull := Z.construct_eq_convexHull_corner
  -- `p ↦ ‖p - d‖` is convex: the triangle inequality with homogeneity
  have hconv : ConvexOn ℝ Set.univ fun p => coeffNorm H (p - d) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have e : a • x + b • y - d = a • (x - d) + b • (y - d) :=
      calc a • x + b • y - d = a • x + b • y - (a + b) • d := by rw [hab, one_smul]
        _ = a • (x - d) + b • (y - d) := by module
    show coeffNorm H (a • x + b • y - d) ≤ a • coeffNorm H (x - d) + b • coeffNorm H (y - d)
    rw [e]
    refine (coeffNorm_add_le H (hH _) (hH _)).trans (le_of_eq ?_)
    rw [coeffNorm_smul H (hH _), coeffNorm_smul H (hH _), abs_of_nonneg ha, abs_of_nonneg hb]
    rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      fun σ => coeffNorm H (Z.corner σ - d)
    refine ⟨Z.corner σ, ?_, hσ.symm⟩
    rw [hhull]
    exact subset_convexHull ℝ _ ⟨σ, rfl⟩
  -- every point is beaten by some corner
  · rintro _ ⟨p, hp, rfl⟩
    rw [hhull] at hp
    obtain ⟨_, ⟨σ, rfl⟩, hle⟩ := hconv.exists_ge_of_mem_convexHull (Set.subset_univ _) hp
    exact hle.trans (Finset.le_sup' (fun σ => coeffNorm H (Z.corner σ - d)) (Finset.mem_univ σ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
