module

public import CORALean.ContSet.Taylm.Real.Operations.LinCoef
public import CORALean.ContSet.Taylm.Real.Operations.HigherTerms
public import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# One step of the linear dominated bounder

Steps (2)-(3) of [1, Sec. 2]'s LDB algorithm on a model over the normalized box, re-expanded at
the box's centre (step (1)): the bound `[M, Min]` of the linear part plus the nonlinear one,
`Min` lowered by the value at the left end and at the mid-point, and in each direction `i` with
`Lᵢ ≠ 0` the part within `d/|Lᵢ|` of the left end kept, `d = Min - M`. The source flips the
coordinates with negative `Lᵢ` (step (2)); here their left end is `+1` instead.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.ldbStep (T : Taylm n) : ℝ × ℝ × (Fin n → ℝ × ℝ) :=
  let c := T.constCoef
  let L := Taylm.linCoef T.terms
  -- the bounds of the linear and the nonlinear part
  let S := ∑ k, |L k|
  let Ih := ((Taylm.polyBounds (Taylm.higherTerms T.terms)).1 + T.remInf,
    (Taylm.polyBounds (Taylm.higherTerms T.terms)).2 + T.remSup)
  let M := c - S + Ih.1
  -- the left end, where the linear part is least, and the mid-point
  let p : Vec ℝ n := fun k => if 0 < L k then -1 else 1
  let Min := min (c + S + Ih.2) (min (T.poly p + T.remSup) (T.poly 0 + T.remSup))
  -- (a): keep in each direction the part within `d / Lᵢ` of the left end
  let d := Min - M
  let R : Fin n → ℝ × ℝ := fun k =>
    if 0 < L k ∧ d / L k < 2 then (-1, -1 + d / L k)
    else if L k < 0 ∧ d / -L k < 2 then (1 - d / -L k, 1) else (-1, 1)
  (M, Min, R)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
