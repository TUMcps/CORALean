import CORALean.ContSet.ZonoBundle.Real.Operations.And

/-!
# `ZonoBundle.and` denotes exactly the intersection

Appending the two families of zonotopes intersects what each bundle denoted:
`Fin.forall_fin_add` splits membership in the appended family the same way
`Fin.append` splits the family itself.

Stays a plain theorem rather than an instance obligation: `Instances` is what
turns it into the `And (ZonoBundle α) α` instance.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.and_exact (zB₁ zB₂ : ZonoBundle α) :
    (zB₁.and zB₂).construct = zB₁.construct ∩ zB₂.construct := by
  ext x
  simp only [ZonoBundle.construct, ZonoBundle.and, Set.mem_iInter, Set.mem_inter_iff,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
