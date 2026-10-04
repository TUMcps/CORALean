import CORALean.ContSet.ProbZonotope.Real.Operations.RepresentsaEmptySet
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct

/-!
# `ProbZonotope.representsaEmptySet` says whether there are no laws

A probabilistic zonotope stands for the family of laws `N(μ, Σ)`, `μ ∈ Z`; it is empty iff
`Z` is, and `Z` always holds its centre.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.representsaEmptySet_iff (P : ProbZonotope n) :
    P.representsaEmptySet = true ↔ P.laws = ∅ := by
  have hne : P.laws.Nonempty := ⟨_, P.Z.c, P.Z.centre_mem_construct, rfl⟩
  simp [ProbZonotope.representsaEmptySet, hne.ne_empty]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
