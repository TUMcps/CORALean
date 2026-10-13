import CORALean.ContSet.ZonoBundle.Real.Operations.Replace

/-!
# What `replace` denotes

Exact: the bundle after replacing member `index` by `Z` denotes `Z` intersected with the
intersection of the other members (those with `i ≠ index`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: `Z` and every member other than `index`. -/
theorem ZonoBundle.replace_construct (zB : ZonoBundle α) (index : Fin zB.k) (Z : Zonotope α) :
    (zB.replace index Z).construct =
      Z.construct ∩ ⋂ i : {i : Fin zB.k // i ≠ index}, (zB.Z i).construct := by -- --- PROOF ---
  ext x
  simp only [ZonoBundle.construct, ZonoBundle.replace, Set.mem_iInter, Set.mem_inter_iff]
  constructor
  · intro h
    refine ⟨by simpa using h index, fun i => ?_⟩
    simpa [Function.update_of_ne i.2] using h i.1
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = index
    · subst hi; simpa using h1
    · simpa [Function.update_of_ne hi] using h2 ⟨i, hi⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
