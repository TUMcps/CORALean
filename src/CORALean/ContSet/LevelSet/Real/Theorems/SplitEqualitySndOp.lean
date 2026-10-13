module

public import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality

@[expose] public section

/-!
# The second part of `splitEquality` holds no equality
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- No constraint of the second part is an equality. -/
theorem LevelSet.splitEquality_snd_op {n : ℕ} (L : LevelSet n)
    (j : Fin L.splitEquality.2.m) : L.splitEquality.2.op j ≠ .eq := by
  have := Finset.orderEmbOfFin_mem (Finset.univ.filter fun i => L.op i ≠ .eq) rfl j
  exact (Finset.mem_filter.mp this).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
