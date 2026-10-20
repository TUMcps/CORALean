module

public import CORALean.HybridDynamics.Parallel.Operations.HPolytopeStackProd
public import CORALean.HybridDynamics.Parallel.Operations.BlockProj

@[expose] public section

/-!
# `HPolytope.stackProd`'s rows at a pair

A row of the product at `⟨i, s⟩` is component `i`'s row `s`, precomposed with block `i`. The
rows are read through `finSigmaFinEquiv.symm`, so this is `Equiv.symm_apply_apply` under the
dependent pair.

## Inputs
* `gs` – halfspace descriptions of the components
* `i` – component
* `s` – row of the component

## Hypotheses
* none

## Conclusion
* product bound is the component's bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {k : ℕ} {n : Fin k → ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.stackProd_b (gs : ∀ i, HPolytope (Vec ℝ (n i))) (i : Fin k)
    (s : Fin (gs i).m) :
    (HPolytope.stackProd gs).b (finSigmaFinEquiv ⟨i, s⟩) =
      (gs i).b s :=
  congrArg (fun p : (Σ i, Fin (gs i).m) => (gs p.1).b p.2) (Equiv.symm_apply_apply _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
