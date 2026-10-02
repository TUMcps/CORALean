import CORALean.ContSet.LevelSet.Real.Operations.Restrict

/-!
# What `restrict` denotes

The points meeting the constraints at the chosen indices.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The restricted level set holds the constraints at the chosen indices. -/
theorem LevelSet.restrict_construct {n : ℕ} (L : LevelSet n) (s : Finset (Fin L.m)) :
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
