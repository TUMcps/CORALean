module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection

@[expose] public section

/-!
# `ZonoBundle.intersection` denotes exactly the intersection

Appending the two families of zonotopes intersects what each bundle denoted [1, Sec. III]:
`Fin.forall_fin_add` splits membership in the appended family the same way
`Fin.append` splits the family itself.

Stays a plain theorem rather than an instance obligation: `Instances` is what
turns it into the `Intersection (ZonoBundle α) α` instance.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.intersection_exact (zB₁ zB₂ : ZonoBundle α) :
    (zB₁.intersection zB₂).construct = zB₁.construct ∩ zB₂.construct := by
  ext x
  simp only [ZonoBundle.construct, ZonoBundle.intersection, Set.mem_iInter, Set.mem_inter_iff,
    Fin.forall_fin_add, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
