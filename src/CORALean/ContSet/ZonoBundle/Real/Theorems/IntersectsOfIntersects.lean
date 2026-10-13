import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

/-!
# Intersection detection: a member that misses the set settles it

[1, Prop. 7] prints `Z_∩ ∩ S ≠ ∅ ↔ ∀ i, Zᵢ ∩ S ≠ ∅`. Only `→` holds, and it is all the
text uses: once one member misses the unsafe set the check is over.
`intersects_of_intersects` is that direction; `NotIntersectsImp` is the other one
failing.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.intersects_of_intersects (zB : ZonoBundle α) (S : Set α)
    (h : (zB.construct ∩ S).Nonempty) (i : Fin zB.k) :
    ((zB.Z i).construct ∩ S).Nonempty :=
  h.mono (Set.inter_subset_inter_left _ (Set.iInter_subset _ i))


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
