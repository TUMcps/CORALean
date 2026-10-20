module

public import CORALean.ContDynamics.LinParamSys.Operations.DependentHomSol
public import CORALean.ContDynamics.LinParamSys.Operations.InputSolutionZono
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrix
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `LinParamSys.initReachInputDependence`, CORA's `initReach_inputDependence` corrected

The first step when the constant input `Uconst = zonotope(U_c, U_G)`, in input coordinates, shares
its parameters with the matrix zonotope `sys.A`: `Rhom_tp` (`dependentHomSol`, corrected) and
`Rhom = enclose(Rinit, Rhom_tp) + F Rinit + inputCorr`, `F` from `priv_tie`, `inputF` from
`priv_inputTie`. The input is `B Uconst ⊕ c` with `B` ranging over the matrix zonotope `sys.B`,
split as `B_c Uconst ⊕ c`, whose generators keep the parameters of `sys.A`, and the deviation
`B_Δ Uconst`, carried by `inputSolutionZono`. **`inputCorr` corrected**: CORA's
`inputF*B*zonotope(uTrans + center(Uconst))` corrects the curvature at the center only, but
`Rhom_tp` integrates all of `Uconst`; here it is `inputF` times `B Uconst ⊕ c`.

## Inputs
* `sys` – system
* `r` – step size
* `η` – Taylor order
* `Rinit` – initial zonotope
* `Uc` – input center
* `UG` – input generators

## Output
* the time-point and time-interval zonotopes of the first step
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
input coordinates by `Uc` and `UG`, at every `B ∈ sys.B`. -/
noncomputable def LinParamSys.initReachInputDependence (sys : LinParamSys 𝕄𝒵 n) (r : ℝ)
    (η : ℕ) (Rinit : Zonotope (Vec ℝ n)) (Uc : Vec ℝ sys.m) (UG : Fin sys.A.h → Vec ℝ sys.m) :
    Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  -- the constant input, in input coordinates
  let Uconst : Zonotope (Vec ℝ sys.m) := ⟨sys.A.h, Uc, UG⟩
  -- its image under `B` at the center of `sys.B`, plus `c`: the generators keep the parameters
  let Vc : Vec ℝ n := sys.B.c *ᵥ Uc + sys.c
  let VG : Fin sys.A.h → Vec ℝ n := fun i => sys.B.c *ᵥ UG i
  let Vdep : Zonotope (Vec ℝ n) := ⟨sys.A.h, Vc, VG⟩
  -- the deviation of `B` from its center, applied to `Uconst`: independent of those parameters
  let BΔ : Zonotope (Mat ℝ n sys.m) := ⟨sys.B.h, 0, sys.B.G⟩
  let Vdev : Zonotope (Vec ℝ n) := Mtimes.mtimes (𝕄 := 𝕄𝒵) (S := 𝒵) BΔ Uconst
  -- time interval error (`priv_tie`) and its input counterpart (`priv_inputTie`)
  let F := MatExp.intervalCorrectionMatrix sys.A.interval r η
  let inputF := MatExp.intervalConstCorrectionMatrix sys.A.interval r η
  -- first time step homogeneous solution
  let Rhom_tp := sys.dependentHomSol r η Rinit Vc VG ⊞ sys.inputSolutionZono (S := 𝒵) r η Vdev
  -- time interval solution
  let inputCorr : Zonotope (Vec ℝ n) :=                                     -- corrected
    Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) inputF (Vdep ⊞ Vdev)
  let Rhom : Zonotope (Vec ℝ n) := LinComb.linComb Rinit Rhom_tp
    ⊞ Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) F Rinit ⊞ inputCorr
  (Rhom_tp, Rhom)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
