module

public import CORALean.HybridDynamics.Parallel.Operations.BlockProj
public import CORALean.ContSet.HPolytope.Real.Theorems.ComapExact

@[expose] public section

/-!
# A guard lifted through a block, exactly

The preimage of a component's guard under the projection onto its block: a constraint on that
block and free elsewhere, which no box can say. `HPolytope.comap_exact` at `blockProj`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.comap_blockProj_exact (c : Fin k) (g : HPolytope (Vec ℝ (n c))) :
    (HPolytope.comap (blockProj c) g).construct = {z | unstack z c ∈ g.construct} :=
  HPolytope.comap_exact _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
