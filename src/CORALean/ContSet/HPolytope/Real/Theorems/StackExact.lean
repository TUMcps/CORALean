module

public import CORALean.ContSet.HPolytope.Real.Operations.Stack

@[expose] public section

/-!
# `HPolytope.stack` is exactly the intersection

Every row of the stack is a row of one member, and every row of a member is a row of the
stack, so a point satisfies all of the one exactly when it satisfies all of the other.
Used by [1, Prop. 4].

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {s : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.stack_exact (P : Fin s → HPolytope α) :
    (HPolytope.stack P).construct = ⋂ i, (P i).construct := by -- --- PROOF ---
  ext x
  simp only [HPolytope.construct, HPolytope.stack, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := h1 (finSigmaFinEquiv ⟨i, j⟩)
      rwa [Equiv.symm_apply_apply] at this
    · have := h2 (finSigmaFinEquiv ⟨i, j⟩)
      rwa [Equiv.symm_apply_apply] at this
  · intro h
    exact ⟨fun r => (h _).1 _, fun r => (h _).2 _⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
