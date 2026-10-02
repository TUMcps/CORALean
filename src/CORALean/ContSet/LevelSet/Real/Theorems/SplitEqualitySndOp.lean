import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality

/-!
# The second part of `splitEquality` holds no equality
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


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
