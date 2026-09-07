import CORALean.ContSet.ZonoBundle.Float.Operations.Reduce

/-!
# `ZonoBundle.reduce` over-approximates the bundle

`Set.iInter_subset` reads a point of every member's set off at the surviving
index, and `Set.subset_iInter` puts that back together over the reduced family —
the intersection over fewer factors is the larger set. No rounding enters: the
surviving members are the ones that arrived, error boxes included.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduce_outer (zB : ZonoBundle 𝕋 n) (o : ℕ) :
    zB.construct ⊆ (zB.reduce o).construct := by
  intro x hx
  simp only [ZonoBundle.construct, Set.mem_iInter] at hx ⊢
  exact fun i => hx (Fin.castLE (min_le_left zB.k o) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
