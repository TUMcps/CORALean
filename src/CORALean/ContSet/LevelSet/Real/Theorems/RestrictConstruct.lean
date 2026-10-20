module

public import CORALean.ContSet.LevelSet.Real.Operations.Restrict

@[expose] public section

/-!
# What `restrict` denotes

The points meeting the constraints at the chosen indices.

## Inputs
* `n` – dimension
* `L` – level set
* `s` – row indices

## Hypotheses
* none

## Conclusion
* the restricted level set holds the rows at `s`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The restricted level set holds the constraints at the chosen indices. -/
theorem LevelSet.restrict_construct {n : ℕ} (L : LevelSet n)
    (s : Finset (Fin L.m)) : -- --- CONCL ---
    (L.restrict s).construct = {x | ∀ i ∈ s, (L.op i).holds (L.f x i)} := by -- --- PROOF ---
  ext x
  constructor
  · intro h i hi
    have hr : i ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hi
    obtain ⟨j, rfl⟩ := hr
    exact h j
  · intro h j
    exact h _ (Finset.orderEmbOfFin_mem s rfl j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
