import CORALean.ContSet.ConPolyZono.Real.Operations.Domain
import CORALean.ContSet.PolyZonotope.Real.Theorems.ContinuousMonomial
import CORALean.ContSet.Zonotope.Real.Theorems.ClosedBallEq

/-!
# The coefficient domain of a constrained polynomial zonotope is compact

Bounded because every factor and every coefficient it admits lies in a unit
cube, so it is a subset of a product of two closed balls, compact because both
factor spaces are finite-dimensional.

Closed is where the constraints are paid for. A constraint row is `A μ(α)`, a
polynomial in the factors and hence continuous, so each of the four families of
conditions cuts out a closed set and the domain is their intersection. This is
what `ConZonotope` gets from a halfspace description instead, and the reason
that argument does not carry over.

Stated apart from `isCompact_construct` because it is about the coefficient
space, whose finite-dimensionality is what the ball argument needs, and not
about the ambient type.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A constraint row is a polynomial in the factors. -/
theorem ConPolyZono.aux_continuous_consRow (C : ConPolyZono α) (i : Fin C.m) :
    Continuous fun ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) =>
      (C.A *ᵥ PolyZonotope.monomial C.EC ab.1) i := by
  have hrow : (fun ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) =>
        (C.A *ᵥ PolyZonotope.monomial C.EC ab.1) i)
      = fun ab => ∑ l, C.A i l * PolyZonotope.monomial C.EC ab.1 l := rfl
  rw [hrow]
  exact continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((PolyZonotope.continuous_monomial C.EC l).comp continuous_fst)

/-- Four families of conditions, each an inequality between continuous
functions, so the domain is a finite intersection of closed sets. -/
theorem ConPolyZono.aux_isClosed_domain (C : ConPolyZono α) : IsClosed C.domain := by
  have hdom : C.domain
      = (⋂ k, {ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) | |ab.1 k| ≤ 1})
        ∩ ((⋂ j, {ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) | |ab.2 j| ≤ 1})
          ∩ ((⋂ i, {ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) |
                C.b.inf i ≤ (C.A *ᵥ PolyZonotope.monomial C.EC ab.1) i})
            ∩ ⋂ i, {ab : (Fin C.p → ℝ) × (Fin C.q → ℝ) |
                (C.A *ᵥ PolyZonotope.monomial C.EC ab.1) i ≤ C.b.sup i})) := by
    ext ab
    -- `forall_and` is what separates a two-sided constraint into two families
    simp only [ConPolyZono.domain, ConPolyZono.satisfies, ConPolyZono.holds,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, forall_and]
  rw [hdom]
  refine IsClosed.inter (isClosed_iInter fun k => ?_)
    (IsClosed.inter (isClosed_iInter fun j => ?_)
      (IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i => ?_)))
  · exact isClosed_le (continuous_abs.comp ((continuous_apply k).comp continuous_fst))
      continuous_const
  · exact isClosed_le (continuous_abs.comp ((continuous_apply j).comp continuous_snd))
      continuous_const
  · exact isClosed_le continuous_const (C.aux_continuous_consRow i)
  · exact isClosed_le (C.aux_continuous_consRow i) continuous_const


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.isCompact_domain (C : ConPolyZono α) : IsCompact C.domain := by
  refine IsCompact.of_isClosed_subset
    ((isCompact_closedBall (0 : Fin C.p → ℝ) 1).prod (isCompact_closedBall (0 : Fin C.q → ℝ) 1))
    C.aux_isClosed_domain fun ab hab => ?_
  -- both cubes are the unit ball of the supremum norm, which is where the bound comes from
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · rw [Zonotope.closedBall_eq]
    exact hab.1
  · rw [Zonotope.closedBall_eq]
    exact hab.2.1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
