module

public import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSol
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `LinParamSys.initReachInputDependence`, CORA's `initReach_inputDependence` corrected

The first step when the constant input `Uconst = zonotope(U_c, U_G)`, in input coordinates,
shares its parameters with the matrix zonotope `sys.A`: the time-point set `Rhom_tp`
(`dependentHomSol`, corrected) and `Rhom = enclose(Rinit, Rhom_tp) + F Rinit + inputCorr`, `F`
from `priv_tie` and `inputF` from `priv_inputTie` (`intervalCorrectionMatrix`,
`intervalConstCorrectionMatrix` of the box). The input is carried to the state space as CORA's
`sys.B*Uconst` and `c` carry it, `B` at its centre `sys.B.c`: the generators keep the
parameters of `sys.A`, which a product with a matrix zonotope's own generators would not.

**`inputCorr` corrected**: CORA's `inputF*B*zonotope(uTrans + center(Uconst))` corrects the
input's curvature over the step at its centre only, but `Rhom_tp` integrates all of `Uconst`;
here `inputF` times the state-space `B Uconst ⊕ c`.

Not modelled: the time-varying input `params.U` (`sys.RV`, added to both sets by CORA), `uTrans`
(zero) and the final `reduce` (an outer step).
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `(Rfirst.tp, Rfirst.ti)` of `initReach_inputDependence`, before `+ sys.RV` and
`reduce`, with the corrected `R_lowOrder` and `inputCorr` over the whole `Uconst`, given in
input coordinates by `Uc` and `UG`. -/
noncomputable def LinParamSys.initReachInputDependence (sys : LinParamSys 𝕄𝒵 n) (r : ℝ)
    (η : ℕ) (Rinit : Zonotope (Vec ℝ n)) (Uc : Vec ℝ sys.m) (UG : Fin sys.A.h → Vec ℝ sys.m) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  -- the constant input in the state space, `B Uconst ⊕ c`, `B` at its centre
  let Vc : Vec ℝ n := sys.B.c *ᵥ Uc + sys.c
  let VG : Fin sys.A.h → Vec ℝ n := fun i => sys.B.c *ᵥ UG i
  let Uconst : Zonotope (Vec ℝ n) := ⟨sys.A.h, Vc, VG⟩
  -- time interval error (`priv_tie`) and its input counterpart (`priv_inputTie`)
  let F := MatExp.intervalCorrectionMatrix sys.A.interval r η
  let inputF := MatExp.intervalConstCorrectionMatrix sys.A.interval r η
  -- first time step homogeneous solution
  let Rhom_tp := sys.dependentHomSol r η Rinit Vc VG
  -- time interval solution
  let inputCorr : Zonotope (Vec ℝ n) :=                                     -- corrected
    Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) inputF Uconst
  let Rhom : Zonotope (Vec ℝ n) := LinComb.linComb Rinit Rhom_tp
    ⊞ Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) F Rinit ⊞ inputCorr
  (Rhom_tp, Rhom)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
