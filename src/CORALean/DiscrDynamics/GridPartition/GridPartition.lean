module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A uniform grid on a box: the representation

CORA's `partition` (`discrDynamics/@partition`): a box, the state space, cut into
`nrOfSegments j` segments along dimension `j`, and so into `∏ j, nrOfSegments j` cells.
The cells are numbered `1, …, N` with the first dimension running fastest, as MATLAB's
`ind2sub` does; the number `0` stands for everything outside the box.

`dividers j k` is CORA's `dividers{j}(k + 1)`, the `k`-th cut of dimension `j` counted from
`0`; only `k ≤ nrOfSegments j` is meaningful. The constructor from an interval and a number
of segments cuts evenly (`ofInterval`), the one from dividers cuts anywhere (`ofDividers`), so
a partition need not be uniform; `WellFormed` asks the dividers not to decrease.

Written once over ℝ, with no float layer: the dividers are real numbers a user supplies or
`linspace` computes, and the cells they bound are boxes whose float enclosure would be a
separate object.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A box cut into cells by `nrOfSegments j` segments along dimension `j`. -/
structure GridPartition (n : ℕ) where
  /-- CORA's `nrOfSegments`. -/
  nrOfSegments : Fin n → ℕ
  /-- CORA's `dividers{j}(k + 1)`, counted from `k = 0`. -/
  dividers : Fin n → ℕ → ℝ

/-- CORA's `intervals`: the state space, from the first to the last divider of each dimension. -/
def GridPartition.intervals (P : GridPartition n) : Real.Interval (Vec ℝ n) where
  inf := fun j => P.dividers j 0
  sup := fun j => P.dividers j (P.nrOfSegments j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
