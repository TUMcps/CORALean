import CORALean.ContSet.ZonoBundle.Real.Operations.Project
import CORALean.ContSet.Zonotope.Real.Theorems.ProjectExact

/-!
# `ZonoBundle.project` over-approximates the projection

Sound because `P (⋂ᵢ Zᵢ) ⊆ ⋂ᵢ P Zᵢ` [1, Prop. 1]: a point in every member projects into every
projected member, `Zonotope.project_exact` reading that image back. Outer only, and CORA's
projection is the same one: projecting an intersection is not the intersection of the
projections.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.project_outer (zB : ZonoBundle (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' zB.construct ⊆ (zB.project dims).construct := by -- --- PROOF ---
  rintro _ ⟨a, ha, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at ha ⊢
  intro i
  show _ ∈ (Zonotope.project (zB.Z i) dims).construct
  rw [← Zonotope.project_exact]
  exact ⟨a, ha i, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
