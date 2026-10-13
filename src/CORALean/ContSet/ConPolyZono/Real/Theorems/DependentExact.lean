module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Dependent
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPadEIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesDependentIff
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Tactic.Abel

@[expose] public section

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
theorem ConPolyZono.aux_sum_dependent (cPZ : ConPolyZono α) (a : Fin (cPZ.p + cPZ.q) → ℝ) :
    (∑ i : Fin (cPZ.h + cPZ.q),
        PolyZonotope.monomial (PolyZonotope.plusE cPZ.E (PolyZonotope.identE cPZ.q)) a i
          • Fin.append cPZ.G cPZ.GI i)
      = (∑ i, PolyZonotope.monomial cPZ.E (fun k => a (Fin.castAdd cPZ.q k)) i • cPZ.G i)
        + ∑ j, a (Fin.natAdd cPZ.p j) • cPZ.GI j := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [PolyZonotope.monomial_plusE_left, Fin.append_left]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [PolyZonotope.monomial_plusE_right, Fin.append_right,
        PolyZonotope.monomial_identE]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.dependent_exact (cPZ : ConPolyZono α) :
    cPZ.construct = cPZ.dependent.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨a, b, ha, hb, hsat, rfl⟩
    have hA : (fun k => Fin.append a b (Fin.castAdd cPZ.q k)) = a :=
      funext fun k => Fin.append_left a b k
    -- forward: the freed coefficients become the right half of the factor vector
    refine ⟨Fin.append a b, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha k) (fun j => by simpa using hb j),
      fun j => j.elim0, ?_, ?_⟩
    · refine (ConPolyZono.satisfies_dependent_iff cPZ _).mpr ?_
      rw [hA]
      exact hsat
    · show cPZ.c + (∑ i, PolyZonotope.monomial cPZ.E a i • cPZ.G i) + ∑ j, b j • cPZ.GI j
          = cPZ.c + (∑ i : Fin (cPZ.h + cPZ.q),
              PolyZonotope.monomial (PolyZonotope.plusE cPZ.E (PolyZonotope.identE cPZ.q))
                (Fin.append a b) i • Fin.append cPZ.G cPZ.GI i)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.aux_sum_dependent]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.append_left,
        Fin.append_right]
      abel
  -- back: the same split read the other way, the independent block now empty
  · rintro _ ⟨a, b, ha, _, hsat, rfl⟩
    refine ⟨fun k => a (Fin.castAdd cPZ.q k), fun j => a (Fin.natAdd cPZ.p j),
      fun k => ha _, fun j => ha _,
      (ConPolyZono.satisfies_dependent_iff cPZ a).mp hsat, ?_⟩
    show cPZ.c + (∑ i : Fin (cPZ.h + cPZ.q),
            PolyZonotope.monomial (PolyZonotope.plusE cPZ.E (PolyZonotope.identE cPZ.q)) a i
              • Fin.append cPZ.G cPZ.GI i)
          + ∑ j : Fin 0, b j • (Fin.elim0 j : α)
        = cPZ.c + (∑ i, PolyZonotope.monomial cPZ.E (fun k => a (Fin.castAdd cPZ.q k)) i • cPZ.G i)
          + ∑ j, a (Fin.natAdd cPZ.p j) • cPZ.GI j
    rw [ConPolyZono.aux_sum_dependent]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
