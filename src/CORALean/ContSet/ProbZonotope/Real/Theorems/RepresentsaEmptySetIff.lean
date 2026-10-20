module

public import CORALean.ContSet.ProbZonotope.Real.Operations.RepresentsaEmptySet
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct

@[expose] public section

/-!
# `ProbZonotope.representsaEmptySet` says whether there are no laws

A probabilistic zonotope stands for the family of laws `N(μ, Σ)`, `μ ∈ Z`; it is empty iff
`Z` is, and `Z` always holds its center.

## Inputs
* `P` – probabilistic zonotope

## Hypotheses
* none

## Conclusion
* `ProbZonotope.representsaEmptySet` says whether there are no laws
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.representsaEmptySet_iff (P : ProbZonotope n) :
    P.representsaEmptySet = true ↔ P.laws = ∅ := by
  have hne : P.laws.Nonempty := ⟨_, P.Z.c, P.Z.center_mem_construct, rfl⟩
  simp [ProbZonotope.representsaEmptySet, hne.ne_empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
