module

public import CORALean.Global.Tensor
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A uniform grid on a box: the representation

CORA's `partition` (`discrDynamics/@partition`): a box, the state space, cut axis-aligned
[1, Sec. 5.1] into `nrOfSegments j` segments along dimension `j`, and so into `∏ j, nrOfSegments j`
cells. The cells are numbered `1, …, N` with the first dimension running fastest, as MATLAB's
`ind2sub` does; the number `0` stands for everything outside the box. `dividers j k` is CORA's
`dividers{j}(k + 1)`; `ofInterval` cuts evenly, `ofDividers` anywhere, and `IsWellFormed` asks the
dividers not to decrease. Written once over ℝ, with no float layer: the cells are boxes whose float
enclosure would be a separate object.

## References

* [1] M. Althoff, N. Kochdumper, T. Ladner, M. Perschl and M. Wetzlinger. "CORA Manual (v2026)".
      Technische Universität München, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
