module

public import CORALean.ContSet.HPolytope.Real.Operations.MoveToEq
public import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct

@[expose] public section

/-!
# The set of `moveToEq`

The inequality rows in `S`, the old equality rows, and the moved rows as equalities.

## Inputs
* `P` – H-polytope
* `S` – inequality rows kept
* `L` – `List (Fin P.m)`

## Hypotheses
* none

## Conclusion
* `moveToEq` denotes the original polytope with the rows in `L` required to hold with equality
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.moveToEq_construct (P : HPolytope α) (S : Finset (Fin P.m))
    (L : List (Fin P.m)) : -- --- CONCL ---
    (P.moveToEq S L).construct
      = {x | (∀ i ∈ S, P.A i x ≤ P.b i) ∧ (∀ r, P.Ae r x = P.be r) ∧
          ∀ i ∈ L, P.A i x = P.b i} := by -- --- PROOF ---
  ext x
  simp only [HPolytope.construct, HPolytope.moveToEq, Set.mem_setOf_eq]
  have h1 : (∀ k : Fin S.card, P.A (S.equivFin.symm k).1 x ≤ P.b (S.equivFin.symm k).1)
      ↔ ∀ i ∈ S, P.A i x ≤ P.b i := by
    constructor
    · intro h i hi
      simpa using h (S.equivFin ⟨i, hi⟩)
    · intro h k
      exact h _ (S.equivFin.symm k).2
  have h2 : (∀ k : Fin (P.me + L.length), (Fin.append P.Ae fun k => P.A (L.get k)) k x
        = (Fin.append P.be fun k => P.b (L.get k)) k)
      ↔ (∀ r, P.Ae r x = P.be r) ∧ ∀ i ∈ L, P.A i x = P.b i := by
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right]
    refine and_congr Iff.rfl ⟨fun h i hi => ?_, fun h k => h _ (List.get_mem L k)⟩
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hi
    exact h k
  rw [h1, h2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
