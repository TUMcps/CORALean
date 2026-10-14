module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as its vertices

Exact, and the one conversion out of a constrained zonotope that loses nothing.

The coefficients live in a halfspace description — the unit box intersected with
the constraints — and that description is bounded, the unit box seeing to it. So
its vertices can be enumerated exactly, and the generators carry each of them to
a point of the set. A combination of coefficients maps to the same combination of
those points, the map being affine and the weights summing to one.

Costs whatever the coefficient domain's enumeration costs, which is `2^m` in its
constraint count. Every cheaper route out of a constrained zonotope drops the
constraints first and pays for it in precision instead.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem ConZonotope.vPolytope_contains (cZ : ConZonotope α) (hne : cZ.domain.construct.Nonempty) :
    cZ.construct ⊆ (cZ.vPolytope hne).construct := by -- --- PROOF ---
  rintro _ ⟨β, hβ, hP, rfl⟩
  obtain ⟨lam, hlam0, hlam1, hlamv⟩ :=
    cZ.domain.vPolytope_contains cZ.isCompact_domain hne (ConZonotope.mem_domain_iff.mpr ⟨hβ, hP⟩)
  refine ⟨lam, hlam0, hlam1, ?_⟩
  -- each coefficient is the same combination of the domain vertices' coefficients
  have hcoef : ∀ j, β j = ∑ l, lam l * ((cZ.domain.vPolytope hne).V l) j := by
    intro j
    rw [hlamv]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hR : ∀ l, lam l • (cZ.c + ∑ j, ((cZ.domain.vPolytope hne).V l) j • cZ.G j)
      = lam l • cZ.c + ∑ j, (lam l * ((cZ.domain.vPolytope hne).V l) j) • cZ.G j := by
    intro l
    rw [smul_add, Finset.smul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => smul_smul _ _ _)
  show cZ.c + ∑ j, β j • cZ.G j
      = ∑ l, lam l • (cZ.c + ∑ j, ((cZ.domain.vPolytope hne).V l) j • cZ.G j)
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hR l, Finset.sum_add_distrib,
    ← Finset.sum_smul, hlam1, one_smul, Finset.sum_comm]
  refine congrArg (fun y => cZ.c + y) (Finset.sum_congr rfl fun j _ => ?_)
  rw [← Finset.sum_smul, ← hcoef j]

-- back: each listed vertex comes from a domain vertex, hence from a point of the set
theorem ConZonotope.contains_vPolytope (cZ : ConZonotope α) (hne : cZ.domain.construct.Nonempty) :
    (cZ.vPolytope hne).construct ⊆ cZ.construct := by -- --- PROOF ---
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ cZ.convex_construct
  rintro _ ⟨l, rfl⟩
  have hd : (cZ.domain.vPolytope hne).V l ∈ cZ.domain.construct :=
    cZ.domain.contains_vPolytope hne (by
      rw [VPolytope.construct_eq_convexHull]
      exact subset_convexHull ℝ _ ⟨l, rfl⟩)
  obtain ⟨hb, hP⟩ := ConZonotope.mem_domain_iff.mp hd
  exact ⟨_, hb, hP, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.vPolytope_exact (cZ : ConZonotope α) (hne : cZ.domain.construct.Nonempty) :
    (cZ.vPolytope hne).construct = cZ.construct :=
  Set.Subset.antisymm (cZ.contains_vPolytope hne) (cZ.vPolytope_contains hne)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
