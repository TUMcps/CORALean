import CORALean.ContSet.ZonoBundle.Real.Operations.And

/-!
# `ZonoBundle.and` denotes exactly the intersection

Appending the two families of zonotopes intersects what each bundle denoted:
`Fin.forall_fin_add` splits membership in the appended family the same way
`Fin.append` splits the family itself.

No `And` class exists to instantiate (#10), so this stays a plain theorem
rather than an instance obligation.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.and_exact (B₁ B₂ : ZonoBundle α) :
    (B₁.and B₂).construct = B₁.construct ∩ B₂.construct := by
  ext x
  simp only [ZonoBundle.construct, ZonoBundle.and, Set.mem_iInter, Set.mem_inter_iff,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
