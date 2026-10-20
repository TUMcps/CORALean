module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Operations.MemDomainIff
public import CORALean.ContSet.ConZonotope.Real.Theorems.Convex
public import CORALean.ContSet.ConZonotope.Real.Theorems.IsCompactDomain
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A constrained zonotope as its vertices

`ConZonotope.vPolytope_contains`: its `vPolytope` contains it.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* `hne` – domain is nonempty

## Conclusion
* set is contained in its vertex polytope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
