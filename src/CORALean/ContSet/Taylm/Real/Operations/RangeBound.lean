module

public import CORALean.ContSet.Taylm.Real.Operations.CodeEval
public import CORALean.ContSet.Taylm.Real.Operations.Bounds
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# Range bounding with Taylor models

[1, Alg. 1], one `let` per printed step: set up the Taylor models of the identity on the box
`D`, evaluate the code list for `f` in Taylor model arithmetic, and bound the range as
`B(P_f) + I_f`. In normalized coordinates the identity is `mid + rad·t`, remainder `[0, 0]`
(`Interval.taylm`). `none` when the evaluation stops at an intrinsic's condition.

## Inputs
* `m` – number of variables
* `e` – code list
* `D` – domain box
* `N` – expansion order

## Output
* enclosure of the range of the code list, if all intrinsics are defined

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.rangeBound {m : ℕ} (e : Taylm.CodeList ℝ m) (D : Interval (Vec ℝ m))
    (N : ℕ) : Option (Interval ℝ) :=
  -- 1. a Taylor model of the identity, with remainder `[0, 0]`
  let TI := D.taylm N
  -- 2. evaluate the code list for `f` in Taylor model arithmetic
  let Pf := Taylm.codeEval N TI e
  -- 3. bound the polynomial and add the remainder, `B(f) = B(P_f) + I_f`
  Pf.map Taylm.bounds

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
