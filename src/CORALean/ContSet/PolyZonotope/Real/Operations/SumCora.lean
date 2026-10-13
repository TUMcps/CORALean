module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sum

@[expose] public section

/-!
# `PolyZonotope.sumCora`: `sum` as CORA's code computes it

`@polyZonotope/sum.m` accumulates the centre in a loop over the list, and the body reads
`c = c + pZlist{1}.c` where it means `pZlist{i}.c`: the first summand's centre is added once
per summand, and no other. Everything else is `sum`; only the centre differs, and it is wrong
as soon as the list has two entries that differ (`sum_cora_counterexample`). Read from the
source, not run.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `sum` with CORA's centre: `pZ.c` plus `(L 0).c` once for each summand. -/
def PolyZonotope.sumCora {m : ℕ} (pZ : PolyZonotope α) (L : Fin m → PolyZonotope α)
    (hp : ∀ i, (L i).p = pZ.p) : PolyZonotope α :=
  { pZ.sum L hp with
    c := pZ.c + if h : 0 < m then ∑ _i : Fin m, (L ⟨0, h⟩).c else 0 }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
