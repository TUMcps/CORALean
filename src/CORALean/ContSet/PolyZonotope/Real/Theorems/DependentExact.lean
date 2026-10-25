module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Making the independent generators dependent loses nothing

[1, Prop. 1]: every polynomial zonotope with independent generators can be written without
them, by expanding the exponent matrix. The fresh factors are what the independent
coefficients were: each occurs in one generator, to the first power, and nowhere else, so it
ranges over `[-1,1]` under no constraint the coefficient did not have (`monomial_identE`).
Both directions are stated through `show`, the counts of the result being projections of a
definition.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* making generators dependent leaves the set unchanged

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to Obtain Subsets of
      Reachable Sets". Proceedings of the 23rd International Conference on Hybrid Systems:
      Computation and Control, 2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The dependent block and the freed one, split apart and each read back
against its own factors. Both inclusions come down to this equation. -/
theorem PolyZonotope.aux_sum_dependent (pZ : PolyZonotope α)
    (a : Fin (pZ.p + pZ.q) → ℝ) : -- --- CONCL ---
    (∑ i : Fin (pZ.h + pZ.q),
        PolyZonotope.monomial (PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q)) a i
          • Fin.append pZ.G pZ.GI i)
      = (∑ i, PolyZonotope.monomial pZ.E (fun k => a (Fin.castAdd pZ.q k)) i • pZ.G i)
        + ∑ j, a (Fin.natAdd pZ.p j) • pZ.GI j := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right,
        PolyZonotope.monomial_identE]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.dependent_exact (pZ : PolyZonotope α) : -- --- CONCL ---
    pZ.construct = pZ.dependent.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    -- forward: the free coefficients become the right half of the factor vector
    refine ⟨Fin.append a b, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha k) (fun j => by simpa using hb j),
      fun j => j.elim0, ?_⟩
    show pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + ∑ j, b j • pZ.GI j
        = pZ.c + (∑ i : Fin (pZ.h + pZ.q),
            PolyZonotope.monomial (PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q))
              (Fin.append a b) i • Fin.append pZ.G pZ.GI i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
    rw [PolyZonotope.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.append_left,
      Fin.append_right]
    abel
  -- back: the same split read the other way, the independent block now empty
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨fun k => a (Fin.castAdd pZ.q k), fun j => a (Fin.natAdd pZ.p j),
      fun k => ha _, fun j => ha _, ?_⟩
    show pZ.c + (∑ i : Fin (pZ.h + pZ.q),
            PolyZonotope.monomial (PolyZonotope.plusE pZ.E (PolyZonotope.identE pZ.q)) a i
              • Fin.append pZ.G pZ.GI i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = pZ.c + (∑ i, PolyZonotope.monomial pZ.E (fun k => a (Fin.castAdd pZ.q k)) i • pZ.G i)
          + ∑ j, a (Fin.natAdd pZ.p j) • pZ.GI j
    rw [PolyZonotope.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
