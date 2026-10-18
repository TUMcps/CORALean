module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Intersection
public import CORALean.ContSet.SetIntersection.Theorems.IntersectionExact
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# `ZonoBundle.intersection` denotes exactly the intersection

Appending the two families of zonotopes intersects what each bundle denoted [1, Sec. III]: the
general `SetIntersection.intersection_exact`, once `List.ofFn_fin_append` reads CORA's appended
cell array `Fin.append` as the appended lists of members.

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
  show ContSet.construct (⟨List.ofFn (Fin.append zB₁.Z zB₂.Z)⟩ : SetIntersection _) = _
  rw [List.ofFn_fin_append]
  exact SetIntersection.intersection_exact zB₁.toSetIntersection zB₂.toSetIntersection

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
