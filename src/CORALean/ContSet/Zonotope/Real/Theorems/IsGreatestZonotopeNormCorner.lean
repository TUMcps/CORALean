module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConstructEqConvexHullCorner
public import CORALean.ContSet.Zonotope.Real.Theorems.ZonotopeNormEquivNorm
public import Mathlib.Tactic.Module
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope

@[expose] public section

/-!
# The containment radius is attained at a corner

`[1, Eq. 47]`, the objective of the optimisation algorithm `opt`:
`d(Z₁, Z₂) = max_{p ∈ Z₁} ‖p - c₂‖_{Z₂}` (the paper's Eq. 19) equals
`max_{x ∈ {-1, 1}^{m₁}} ‖G₁ x + c₁ - c₂‖_{Z₂}`. The maximum of a convex function over the
convex hull of the corners is attained at a corner (`ConvexOn.exists_ge_of_mem_convexHull`),
`‖·‖_{Z₂}` being convex (`[1, Cor. 3]`). The printed `G₂ x` is `G₁ x`: the corners are the
inbody's.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.isGreatest_zonotopeNorm_corner (Z₁ Z₂ : Zonotope (Vec ℝ n))
    (hG : Function.Surjective Z₂.genMap) : -- --- STMT ---
    IsGreatest ((fun p => Z₂.zonotopeNorm (p - Z₂.c)) '' Z₁.construct)
      (Finset.univ.sup' Finset.univ_nonempty fun σ =>
        Z₂.zonotopeNorm (Z₁.corner σ - Z₂.c)) := by -- --- PROOF ---
  have hhull := Z₁.construct_eq_convexHull_corner
  -- `p ↦ ‖p - c₂‖` is convex, a translate of the norm
  have hconv : ConvexOn ℝ Set.univ fun p => Z₂.zonotopeNorm (p - Z₂.c) := by
    have h := (Z₂.zonotopeNorm_equiv_norm hG).2.1
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have e : a • x + b • y - Z₂.c = a • (x - Z₂.c) + b • (y - Z₂.c) :=
      calc a • x + b • y - Z₂.c = a • x + b • y - (a + b) • Z₂.c := by rw [hab, one_smul]
        _ = a • (x - Z₂.c) + b • (y - Z₂.c) := by module
    show Z₂.zonotopeNorm (a • x + b • y - Z₂.c)
      ≤ a • Z₂.zonotopeNorm (x - Z₂.c) + b • Z₂.zonotopeNorm (y - Z₂.c)
    rw [e]
    exact h.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  refine ⟨?_, ?_⟩
  -- the largest corner value is a value at a point of `Z₁`
  · obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      fun σ => Z₂.zonotopeNorm (Z₁.corner σ - Z₂.c)
    refine ⟨Z₁.corner σ, ?_, hσ.symm⟩
    rw [hhull]
    exact subset_convexHull ℝ _ ⟨σ, rfl⟩
  -- and every point is beaten by some corner
  · rintro _ ⟨p, hp, rfl⟩
    rw [hhull] at hp
    obtain ⟨_, ⟨σ, rfl⟩, hle⟩ := hconv.exists_ge_of_mem_convexHull (Set.subset_univ _) hp
    exact hle.trans (Finset.le_sup' (fun σ => Z₂.zonotopeNorm (Z₁.corner σ - Z₂.c))
      (Finset.mem_univ σ))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
