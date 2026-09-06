import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Interval.Real.Operations.IsNonempty

/-!
# `IsNonempty` is nonemptiness

`inf` is the witness one way, transitivity through any point the other. Negated
in `NotIsNonempty`, it is the claim that crossed bounds denote `∅`.
-/

-- Authors:       Tobias Ladner
-- Written:       17-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.isNonempty_iff (I : Interval α) : I.IsNonempty ↔ I.construct.Nonempty := by
  constructor
  · exact fun h => ⟨I.inf, fun i => ⟨le_refl _, h i⟩⟩
  · rintro ⟨x, hx⟩ i
    exact le_trans (hx i).1 (hx i).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
