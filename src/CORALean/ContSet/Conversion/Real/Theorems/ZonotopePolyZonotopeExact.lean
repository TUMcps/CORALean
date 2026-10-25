module

public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope

@[expose] public section

/-!
# A zonotope as a polynomial zonotope

The construction is [1, Prop. 3]. Exact: give each generator a factor of its own, appearing in that
generator alone and to the first power, and every monomial collapses to the coefficient it stands
for. The exponent matrix is the identity, and `GI` is empty. Read the other way, a polynomial
zonotope is a zonotope exactly when its exponent matrix can be brought to this shape. Both
directions are stated through `show`, as the counts of the result are projections of a definition.
Composed with `PolyZonotope.quadMap_exact`, this is half of [2, Thm. 1]: a zonotope's quadratic-map
image is exactly a polynomial zonotope.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope equals its polynomial zonotope

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
* [2] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control, 2013.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   12-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.polyZonotope_exact (Z : Zonotope α) : -- --- CONCL ---
    Z.construct = Z.polyZonotope.construct := by -- --- PROOF ---
  have hsum : ∀ a : Fin Z.h → ℝ,
      (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) a i • Z.G i)
        = ∑ j, a j • Z.G j :=
    fun a => Finset.sum_congr rfl fun i _ => by rw [PolyZonotope.monomial_identE]
  -- both directions off `hsum`: identity exponents make every monomial a factor
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    refine ⟨β, fun _ => 0, hβ, fun j => j.elim0, ?_⟩
    show Z.c + ∑ j, β j • Z.G j
        = Z.c + (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) β i • Z.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [hsum]
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨a, ha, ?_⟩
    show Z.c + (∑ i : Fin Z.h, PolyZonotope.monomial (PolyZonotope.identE Z.h) a i • Z.G i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = Z.c + ∑ j, a j • Z.G j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [hsum]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
