import CORALean.ContDynamics.LinParamSys.Operations.InitReachInputDependence
import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

/-!
# `NonlinParamSys.linReachCora`, one step of `linReach` with an interval `paramInt`

The path `reach(nonlinParamSys)` takes with `paramInt` an interval: `@contDynamics/linReach.m` [2]
calls `linearize` [1] (`NonlinParamSys.linearize`), translates the initial set by the
linearization point, and, as `isa(sys,'nonlinParamSys') && isa(params.paramInt,'interval')`,
runs `initReach_inputDependence` on the `linParamSys` of `zA` with the constant input `zf`
(`LinParamSys.initReachInputDependence`, corrected where CORA's `inputCorr` is too small; for the
zero matrix `zA` of the counterexample the two coincide), then translates back and adds the
abstraction error `Rerror`.

Not modelled: the time-varying input `zB (U + uTrans - p.u)` (`linParams.U`), the choice of the
linearization point, and the computation of `Rerror` by the Lagrange remainder over the enclosing
set with its tightening loop, which is a parameter here.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
* [2] `contDynamics/@contDynamics/linReach.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `(Rtp, Rti)` of `linReach` for one step `r` at Taylor order `η`, from `Rinit` about
`(xs, us)` over the parameter box `paramInt`, with abstraction error `Rerror`. -/
noncomputable def NonlinParamSys.linReachCora (sys : NonlinParamSys n m q) (xs : Vec ℝ n)
    (us : Vec ℝ m) (paramInt : Interval (Vec ℝ q)) (Rinit : Zonotope (Vec ℝ n))
    (Rerror : Zonotope (Vec ℝ n)) (r : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  -- [sys,linsys,linParams,linOptions] = linearize(sys,Rinit,params,options);
  let lin := sys.linearize xs us paramInt
  let linsys : LinParamSys 𝕄𝒵 n := ⟨lin.zA⟩
  -- Rdelta = Rinit + (-sys.linError.p.x);
  let Rdelta : Zonotope (Vec ℝ n) := Rinit ⊞ Zonotope.ofPoint (-lin.xs)
  -- [linsys,R] = initReach_inputDependence(linsys,Rdelta,linParams,linOptions);
  let R := linsys.initReachInputDependence r η Rdelta lin.zf.c lin.zf.G
  -- Rti = Rti+sys.linError.p.x;  Rtp = Rtp+sys.linError.p.x;
  let Rtp := R.1 ⊞ Zonotope.ofPoint lin.xs
  let Rti := R.2 ⊞ Zonotope.ofPoint lin.xs
  -- Rti=Rti+Rerror;  Rtp=Rtp+Rerror;
  (Rtp ⊞ Rerror, Rti ⊞ Rerror)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
