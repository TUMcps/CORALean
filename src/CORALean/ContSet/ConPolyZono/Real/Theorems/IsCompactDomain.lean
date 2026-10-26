module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEqUnit
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
public import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq
public import Mathlib.Analysis.Normed.Order.Lattice
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq

@[expose] public section

/-!
# The coefficient domain of a constrained polynomial zonotope is compact

Bounded because every factor and every coefficient it admits lies in a unit cube, a subset of a
product of two closed balls in finite-dimensional spaces.

Closed is where the constraints are paid for. A constraint row is `A μ(α)`, a polynomial in the
factors and hence continuous, so each family of conditions cuts out a closed set and the domain is
their intersection; `ConZonotope` gets this from a halfspace description instead. Stated apart
from `isCompact_construct` because it is about the coefficient space.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the coefficient domain is compact
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A constraint row is a polynomial in the factors. -/
private theorem ConPolyZono.aux_continuous_consRow (cPZ : ConPolyZono α)
    (i : Fin cPZ.cons.m) : -- --- CONCL ---
    Continuous fun ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ) =>
      (cPZ.cons.A *ᵥ PolyZonotope.monomial cPZ.cons.R ab.1) i := by -- --- PROOF ---
  have hrow : (fun ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ) =>
        (cPZ.cons.A *ᵥ PolyZonotope.monomial cPZ.cons.R ab.1) i)
      = fun ab => ∑ l, cPZ.cons.A i l * PolyZonotope.monomial cPZ.cons.R ab.1 l := rfl
  rw [hrow]
  exact continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((PolyZonotope.continuous_monomial cPZ.cons.R l).comp continuous_fst)

/-- Three families of conditions, each an inequality or an equation between continuous
functions, so the domain is a finite intersection of closed sets. -/
private theorem ConPolyZono.aux_isClosed_domain (cPZ : ConPolyZono α) : -- --- CONCL ---
    IsClosed cPZ.domain := by -- --- PROOF ---
  have hdom : cPZ.domain
      = (⋂ j, {ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ) | |ab.2 j| ≤ 1})
        ∩ ((⋂ k, {ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ) | |ab.1 k| ≤ 1})
          ∩ ⋂ i, {ab : (Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ) |
                (cPZ.cons.A *ᵥ PolyZonotope.monomial cPZ.cons.R ab.1) i = cPZ.cons.b i}) := by
    ext ab
    simp only [ConPolyZono.domain,
      PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hdom]
  refine IsClosed.inter (isClosed_iInter fun j => ?_)
    (IsClosed.inter (isClosed_iInter fun k => ?_)
      (isClosed_iInter fun i => ?_))
  · exact isClosed_le (continuous_abs.comp ((continuous_apply j).comp continuous_snd))
      continuous_const
  · exact isClosed_le (continuous_abs.comp ((continuous_apply k).comp continuous_fst))
      continuous_const
  · exact isClosed_eq (cPZ.aux_continuous_consRow i) continuous_const


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isCompact_domain (cPZ : ConPolyZono α) : -- --- CONCL ---
    IsCompact cPZ.domain := by -- --- PROOF ---
  refine IsCompact.of_isClosed_subset
    ((isCompact_closedBall (0 : Fin cPZ.p → ℝ) 1).prod
      (isCompact_closedBall (0 : Fin cPZ.qI → ℝ) 1))
    cPZ.aux_isClosed_domain fun ab hab => ?_
  -- both cubes are the unit ball of the supremum norm, which is where the bound comes from
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · rw [Zonotope.closedBall_eq]
    exact ((PolyLevelSet.mem_construct_iff_of_eq_unit cPZ.cons_eq cPZ.cons_dom).mp hab.2).1
  · rw [Zonotope.closedBall_eq]
    exact hab.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
