module

public import CORALean.ContSet.HPolytope.Real.Operations.Restrict

@[expose] public section

/-!
# The set of a restricted polytope

Only the constraints whose rows were kept: `x` is in `P.restrict S T` exactly when it satisfies
the inequality rows in `S` and the equality rows in `T`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.restrict_construct (P : HPolytope α) (S : Finset (Fin P.m))
    (T : Finset (Fin P.me)) :
    (P.restrict S T).construct
      = {x | (∀ i ∈ S, P.A i x ≤ P.b i) ∧ ∀ r ∈ T, P.Ae r x = P.be r} := by -- --- PROOF ---
  ext x
  simp only [HPolytope.construct, HPolytope.restrict, Set.mem_setOf_eq]
  have h1 : (∀ k : Fin S.card, P.A (S.equivFin.symm k).1 x ≤ P.b (S.equivFin.symm k).1)
      ↔ ∀ i ∈ S, P.A i x ≤ P.b i := by
    constructor
    · intro h i hi
      simpa using h (S.equivFin ⟨i, hi⟩)
    · intro h k
      exact h _ (S.equivFin.symm k).2
  have h2 : (∀ k : Fin T.card, P.Ae (T.equivFin.symm k).1 x = P.be (T.equivFin.symm k).1)
      ↔ ∀ r ∈ T, P.Ae r x = P.be r := by
    constructor
    · intro h r hr
      simpa using h (T.equivFin ⟨r, hr⟩)
    · intro h k
      exact h _ (T.equivFin.symm k).2
  rw [h1, h2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
