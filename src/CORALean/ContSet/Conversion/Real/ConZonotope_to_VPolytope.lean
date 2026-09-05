import CORALean.ContSet.ConZonotope.Real.Operations.Domain
import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
import CORALean.ContSet.Conversion.Real.HPolytope_to_VPolytope
import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

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

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

noncomputable def ConZonotope.vPolytope (C : ConZonotope α)
    (hne : C.domain.construct.Nonempty) : VPolytope α where
  k := (C.domain.vPolytope hne).k
  V := fun l => C.c + ∑ j, ((C.domain.vPolytope hne).V l) j • C.G j

theorem ConZonotope.subset_vPolytope (C : ConZonotope α) (hne : C.domain.construct.Nonempty) :
    C.construct ⊆ (C.vPolytope hne).construct := by
  rintro _ ⟨β, hβ, hP, rfl⟩
  obtain ⟨lam, hlam0, hlam1, hlamv⟩ :=
    C.domain.subset_vPolytope C.isCompact_domain hne (ConZonotope.mem_domain_iff.mpr ⟨hβ, hP⟩)
  refine ⟨lam, hlam0, hlam1, ?_⟩
  -- each coefficient is the same combination of the domain vertices' coefficients
  have hcoef : ∀ j, β j = ∑ l, lam l * ((C.domain.vPolytope hne).V l) j := by
    intro j
    rw [hlamv]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hR : ∀ l, lam l • (C.c + ∑ j, ((C.domain.vPolytope hne).V l) j • C.G j)
      = lam l • C.c + ∑ j, (lam l * ((C.domain.vPolytope hne).V l) j) • C.G j := by
    intro l
    rw [smul_add, Finset.smul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => smul_smul _ _ _)
  show C.c + ∑ j, β j • C.G j
      = ∑ l, lam l • (C.c + ∑ j, ((C.domain.vPolytope hne).V l) j • C.G j)
  rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hR l, Finset.sum_add_distrib,
    ← Finset.sum_smul, hlam1, one_smul, Finset.sum_comm]
  refine congrArg (fun y => C.c + y) (Finset.sum_congr rfl fun j _ => ?_)
  rw [← Finset.sum_smul, ← hcoef j]

-- back: each listed vertex comes from a domain vertex, hence from a point of the set
theorem ConZonotope.vPolytope_subset (C : ConZonotope α) (hne : C.domain.construct.Nonempty) :
    (C.vPolytope hne).construct ⊆ C.construct := by
  rw [VPolytope.construct_eq_convexHull]
  refine convexHull_min ?_ C.convex_construct
  rintro _ ⟨l, rfl⟩
  have hd : (C.domain.vPolytope hne).V l ∈ C.domain.construct :=
    C.domain.vPolytope_subset hne (by
      rw [VPolytope.construct_eq_convexHull]
      exact subset_convexHull ℝ _ ⟨l, rfl⟩)
  obtain ⟨hb, hP⟩ := ConZonotope.mem_domain_iff.mp hd
  exact ⟨_, hb, hP, rfl⟩

theorem ConZonotope.vPolytope_exact (C : ConZonotope α) (hne : C.domain.construct.Nonempty) :
    (C.vPolytope hne).construct = C.construct :=
  Set.Subset.antisymm (C.vPolytope_subset hne) (C.subset_vPolytope hne)

end CORALean.Real
