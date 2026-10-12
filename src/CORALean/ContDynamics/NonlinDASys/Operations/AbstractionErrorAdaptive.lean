import CORALean.ContDynamics.NonlinDASys.Operations.LinError
import CORALean.ContDynamics.NonlinDASys.Definitions.HessData
import CORALean.ContDynamics.NonlinDASys.Definitions.AbstractionError
import CORALean.ContSet.Zonotope.Real.Operations.AbsBound

/-!
# `NonlinDASys.abstractionErrorAdaptive`

CORA's `private/priv_abstractionError_adaptive` for `tensorOrder == 2`: the errors of
[1, Cor. 1] over `dz = [dx; dy; du]`, the dynamics' `Z_error_x`, the constraint's `Z_error_y`, and
`Z_error`, with the sizes `errorInt_x`, `errorInt_y`, `errorInt`. CORA's `Z_error = Z_error_x +
CF_inv Z_error_y` adds the algebraic error where the linearized DAE subtracts it (FINDINGS.md);
here it is `Z_error_x - CF_inv Z_error_y`, `NonlinDASys.linError`. The Hessian intervals are
data (`nlnsysDA.hessian`), `R_y` the joint set of the pass run with `Z_error_y`, the third-order
branch is not formalized. CORA's tuning.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n p m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `priv_abstractionError_adaptive`, `tensorOrder == 2`, at the Hessian intervals `H`. -/
noncomputable def NonlinDASys.abstractionErrorAdaptive (CF_inv : Mat ℝ n p)
    (H : NonlinDASys.HessData n p q) : NonlinDASys.AbstractionError n p :=
  let Z_error_x : Zonotope (Vec ℝ n) :=                                  -- Z_error_x
    NonlinDASys.linError H.Hd_c H.Hd_Δ H.Ha_c H.Ha_Δ (0 : Mat ℝ n p) H.dz
  let Z_error_y : Zonotope (Vec ℝ p) :=                                  -- Z_error_y
    NonlinDASys.linError (n := p) (p := 0) H.Ha_c H.Ha_Δ Fin.elim0 Fin.elim0 (0 : Mat ℝ p 0) H.dz
  let Z_error : Zonotope (Vec ℝ n) :=                                    -- Z_error, corrected sign
    NonlinDASys.linError H.Hd_c H.Hd_Δ H.Ha_c H.Ha_Δ CF_inv H.dz
  { Z_error_x := Z_error_x, Z_error_y := Z_error_y, Z_error := Z_error,
    errorInt_x := fun i => Z_error_x.absBound i,                         -- errorInt_x
    errorInt_y := fun j => Z_error_y.absBound j,                         -- errorInt_y
    errorInt := fun i => Z_error.absBound i }                            -- errorInt

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
