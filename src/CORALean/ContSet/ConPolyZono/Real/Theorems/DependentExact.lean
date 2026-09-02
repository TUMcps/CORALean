import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent

/-!
# Making the independent generators dependent loses nothing

The fresh factors are what the independent coefficients were: each occurs in one
generator, to the first power, and in no constraint row, so it ranges over
`[-1,1]` under nothing the coefficient did not already answer to.
`monomial_identE` says the first part and `holds_padE_iff` the second.

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
theorem ConPolyZono.aux_sum_dependent (C : ConPolyZono α) (a : Fin (C.p + C.q) → ℝ) :
    (∑ i : Fin (C.h + C.q),
        PolyZonotope.monomial (PolyZonotope.plusE C.E (PolyZonotope.identE C.q)) a i
          • Fin.append C.G C.GI i)
      = (∑ i, PolyZonotope.monomial C.E (fun k => a (Fin.castAdd C.q k)) i • C.G i)
        + ∑ j, a (Fin.natAdd C.p j) • C.GI j := by
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right,
        PolyZonotope.monomial_identE]

theorem ConPolyZono.dependent_exact (C : ConPolyZono α) :
    C.construct = C.dependent.construct := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, hsat, rfl⟩
    have hA : (fun k => Fin.append a b (Fin.castAdd C.q k)) = a :=
      funext fun k => Fin.append_left a b k
    refine ⟨Fin.append a b, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha k) (fun j => by simpa using hb j),
      fun j => j.elim0, ?_, ?_⟩
    · refine (ConPolyZono.satisfies_dependent_iff C _).mpr ?_
      rw [hA]
      exact hsat
    · show C.c + (∑ i, PolyZonotope.monomial C.E a i • C.G i) + ∑ j, b j • C.GI j
          = C.c + (∑ i : Fin (C.h + C.q),
              PolyZonotope.monomial (PolyZonotope.plusE C.E (PolyZonotope.identE C.q))
                (Fin.append a b) i • Fin.append C.G C.GI i)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.aux_sum_dependent]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.append_left,
        Fin.append_right]
      abel
  · rintro _ ⟨a, b, ha, _, hsat, rfl⟩
    refine ⟨fun k => a (Fin.castAdd C.q k), fun j => a (Fin.natAdd C.p j),
      fun k => ha _, fun j => ha _,
      (ConPolyZono.satisfies_dependent_iff C a).mp hsat, ?_⟩
    show C.c + (∑ i : Fin (C.h + C.q),
            PolyZonotope.monomial (PolyZonotope.plusE C.E (PolyZonotope.identE C.q)) a i
              • Fin.append C.G C.GI i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = C.c + (∑ i, PolyZonotope.monomial C.E (fun k => a (Fin.castAdd C.q k)) i • C.G i)
          + ∑ j, a (Fin.natAdd C.p j) • C.GI j
    rw [ConPolyZono.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    abel

end CORALean.Real
