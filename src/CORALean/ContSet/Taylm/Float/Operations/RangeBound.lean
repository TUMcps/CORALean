import CORALean.ContSet.Taylm.Float.Operations.CodeEval
import CORALean.ContSet.Taylm.Float.Operations.Bounds
import CORALean.ContSet.Conversion.Float.Interval_to_Taylm

/-!
# Range bounding with floating-point Taylor models

[1, Alg. 1] run in floats, one `let` per printed step: the Taylor models of the identity on the
box `D`, the code list evaluated in floating-point Taylor model arithmetic, and the range bound
`B(P_f) + I_f` rounded outward. `none` when the evaluation stops at an intrinsic.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.rangeBound {m : ℕ} (p q s : ℕ) (e : Real.Taylm.CodeList 𝕋 m)
    (D : Interval (Vec 𝕋 m)) (N : ℕ) : Option (𝕋 × 𝕋) :=
  -- 1. a Taylor model of the identity, with remainder `[0, 0]`
  let TI := D.taylm N
  -- 2. evaluate the code list for `f` in Taylor model arithmetic
  let Pf := Taylm.codeEval p q s N TI e
  -- 3. bound the polynomial and add the remainder, `B(f) = B(P_f) + I_f`
  Pf.map Taylm.bounds

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
