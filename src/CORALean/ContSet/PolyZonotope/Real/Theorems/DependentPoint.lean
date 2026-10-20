module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# Making the independent generators dependent, at one factor vector

[1, Prop. 1]: at the factor vector `(a, b)`, the dependent set's point is the old point at `a`
plus the independent generators weighted by `b`: the coefficients become the fresh factors, in
order, after the old ones. `dependent_exact` says the sets agree; this is the same fact with the
factors named, which a chain of steps that keeps one factor vector needs.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values
* `b` – independent values

## Hypotheses
* none

## Conclusion
* the dependent point is the original point plus the independent part

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The point of `dependent` at `(a, b)` is the old point at `a` plus the weighted independent
generators. -/
theorem PolyZonotope.dependent_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ)
    (b : Fin pZ.q → ℝ) : -- --- CONCL ---
    pZ.dependent.point (Fin.append a b) = pZ.point a + ∑ j, b j • pZ.GI j := by -- --- PROOF ---
  show pZ.c + ∑ i : Fin (pZ.h + pZ.q), PolyZonotope.monomial
      (PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q)) (Fin.append a b) i
        • Fin.append pZ.G pZ.GI i = pZ.c + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
          + ∑ j, b j • pZ.GI j
  rw [Fin.sum_univ_add, add_assoc]
  congr 2
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
      simp only [Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right, PolyZonotope.monomial_identE]
      simp only [Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
