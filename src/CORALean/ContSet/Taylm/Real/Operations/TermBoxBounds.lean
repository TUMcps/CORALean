module

public import CORALean.ContSet.Taylm.Real.Operations.PowBounds
public import CORALean.ContSet.Taylm.Real.Operations.ProdBounds

@[expose] public section

/-!
# A term's bounds over a box by interval arithmetic

One summand of [1, Eq. 12]: the coefficient times the interval product of the coordinates'
interval powers.

## Inputs
* `B` – box
* `a` – term

## Output
* range of the term over the box by interval arithmetic

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.termBoxBounds (B : Fin n → Interval ℝ) (a : ℝ × (Fin n → ℕ)) : Interval ℝ :=
  let M := Taylm.prodBounds (List.ofFn fun k => Taylm.powBounds (B k).inf (B k).sup (a.2 k))
  ⟨Interval.mulLo a.1 a.1 M.inf M.sup, Interval.mulHi a.1 a.1 M.inf M.sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
