import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce

/-!
# `ZonoBundle.reduce` over-approximates the bundle

`Set.iInter_subset` reads a point of every component's set off at the
surviving index, and `Set.subset_iInter` puts that back together over the
reduced family — the intersection over fewer factors is the larger set.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduce_outer (B : ZonoBundle α) (o : ℕ) :
    B.construct ⊆ (B.reduce o).construct := by
  intro x hx
  simp only [ZonoBundle.construct, Set.mem_iInter] at hx ⊢
  exact fun i => hx (Fin.castLE (min_le_left B.k o) i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
