import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE

/-!
# Making the independent generators dependent loses nothing

The fresh factors are what the independent coefficients were: each occurs in one
generator, to the first power, and nowhere else, so it ranges over `[-1,1]`
under no constraint the coefficient did not already have. `monomial_identE` is
the line that says so.

Both directions are stated through `show`, since the counts of the result are
projections of a definition and the sum lemmas match only in their reduced
spelling.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The dependent block and the freed one, split apart and each read back
against its own factors. Both inclusions come down to this equation. -/
theorem PolyZonotope.aux_sum_dependent (PZ : PolyZonotope α) (a : Fin (PZ.p + PZ.q) → ℝ) :
    (∑ i : Fin (PZ.h + PZ.q),
        PolyZonotope.monomial (PolyZonotope.plusE PZ.E (PolyZonotope.identE PZ.q)) a i
          • Fin.append PZ.G PZ.GI i)
      = (∑ i, PolyZonotope.monomial PZ.E (fun k => a (Fin.castAdd PZ.q k)) i • PZ.G i)
        + ∑ j, a (Fin.natAdd PZ.p j) • PZ.GI j := by
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right,
        PolyZonotope.monomial_identE]

theorem PolyZonotope.dependent_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.dependent.construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    -- forward: the free coefficients become the right half of the factor vector
    refine ⟨Fin.append a b, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha k) (fun j => by simpa using hb j),
      fun j => j.elim0, ?_⟩
    show PZ.c + (∑ i, PolyZonotope.monomial PZ.E a i • PZ.G i) + ∑ j, b j • PZ.GI j
        = PZ.c + (∑ i : Fin (PZ.h + PZ.q),
            PolyZonotope.monomial (PolyZonotope.plusE PZ.E (PolyZonotope.identE PZ.q))
              (Fin.append a b) i • Fin.append PZ.G PZ.GI i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
    rw [PolyZonotope.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.append_left,
      Fin.append_right]
    abel
  -- back: the same split read the other way, the independent block now empty
  · rintro _ ⟨a, b, ha, _, rfl⟩
    refine ⟨fun k => a (Fin.castAdd PZ.q k), fun j => a (Fin.natAdd PZ.p j),
      fun k => ha _, fun j => ha _, ?_⟩
    show PZ.c + (∑ i : Fin (PZ.h + PZ.q),
            PolyZonotope.monomial (PolyZonotope.plusE PZ.E (PolyZonotope.identE PZ.q)) a i
              • Fin.append PZ.G PZ.GI i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = PZ.c + (∑ i, PolyZonotope.monomial PZ.E (fun k => a (Fin.castAdd PZ.q k)) i • PZ.G i)
          + ∑ j, a (Fin.natAdd PZ.p j) • PZ.GI j
    rw [PolyZonotope.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    abel

end CORALean.Real
