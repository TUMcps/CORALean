module

public import CORALean.ContSet.Taylm.Real.Operations.GlobalMin
public import CORALean.ContSet.Taylm.Real.Operations.GoLowerBound

@[expose] public section

/-!
# `Taylm.cosyGo`

[1, Sec. 4]'s verified global optimizer on a model over a sub-box `X` of the normalized box:
COSY-GO's box steps with its bound of a box, and the mid-point estimate `P(p) + sup I`.

## Inputs
* `T` – Taylor model
* `X` – sub-box
* `ε` – tolerance
* `ldbFuel` – fuel of the linear bounder
* `fuel` – step budget

## Output
* verified enclosure of the model's minimum

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range Bounders".
      2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.cosyGo (T : Taylm n) (X : Fin n → Interval ℝ) (ε : ℝ) (ldbFuel fuel : ℕ) :
    Interval ℝ :=
  Taylm.globalMin (T.goLowerBound ε ldbFuel) (fun p => T.poly p + T.rem.sup) X fuel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
