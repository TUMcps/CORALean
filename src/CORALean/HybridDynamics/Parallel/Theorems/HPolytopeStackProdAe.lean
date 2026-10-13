module

public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj

@[expose] public section

/-!
# `HPolytope.stackProd`'s rows at a pair

A row of the product at `⟨i, s⟩` is component `i`'s row `s`, precomposed with block `i`. The
rows are read through `finSigmaFinEquiv.symm`, so this is `Equiv.symm_apply_apply` under the
dependent pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.stackProd_Ae (gs : ∀ i, HPolytope (Vec ℝ (n i))) (i : Fin k)
    (s : Fin (gs i).me) :
    (HPolytope.stackProd gs).Ae (finSigmaFinEquiv ⟨i, s⟩) =
      ((gs i).Ae s).comp (blockProj i) :=
  congrArg (fun p : (Σ i, Fin (gs i).me) => ((gs p.1).Ae p.2).comp (blockProj p.1))
    (Equiv.symm_apply_apply _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
