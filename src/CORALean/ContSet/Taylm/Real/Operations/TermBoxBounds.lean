module

public import CORALean.ContSet.Taylm.Real.Operations.PowBounds
public import CORALean.ContSet.Taylm.Real.Operations.ProdBounds

@[expose] public section

/-!
# A term's bounds over a box by interval arithmetic

One summand of [1, Eq. 12]: the coefficient times the interval product of the coordinates'
interval powers.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.termBoxBounds (B : Fin n → ℝ × ℝ) (a : ℝ × (Fin n → ℕ)) : ℝ × ℝ :=
  let M := Taylm.prodBounds (List.ofFn fun k => Taylm.powBounds (B k).1 (B k).2 (a.2 k))
  (Interval.mulLo a.1 a.1 M.1 M.2, Interval.mulHi a.1 a.1 M.1 M.2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
