module

public import CORALean.ContDynamics.LinProbSys.Definitions.PostState
public import CORALean.ContDynamics.LinProbSys.Operations.InputCov
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.MatMul
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.ProbZonotope.Real.Operations.Enclose
public import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ProbZonotope.Real.Operations.Plus
public import CORALean.ContSet.ProbZonotope.Real.Operations.Zonotope
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# The first step of the probabilistic reach loop

CORA's `linProbSys/initReach` [1] with its three private helpers inlined, line by line, the
sign of the noise covariance corrected. `priv_pexpm` is `e^{Ar}` and the remainder bound,
`priv_tie` the correction matrix `F` (`MatExp.correctionMatrix`), `priv_inputSolution` the
input solution of `B U` (`LinearSys.inputSolution`: `Vsum` plus `E r V`), the constant
input's `A⁻¹(e^{Ar} - I) B uTrans`, its correction `A⁻¹ F B uTrans` unless `originContained`,
and the probabilistic input solution: a probabilistic zonotope at the origin whose covariance
is `inputCov`, CORA's `Sigma` with `e^{(λ_i+λ_j)r} - 1` in place of `1 - e^{-(λ_i+λ_j)r}`. The
eigendecomposition `[V,W] = eig(A)` is the argument `(V, λ)`.

The output is `(Rfirst.tp, Rfirst.ti, options, pRinput)`: the time-point and time-interval
sets, the four sets `post` reads from `options`, and `obj.taylor.pRinput`, which `post` reads
from the object. `gammaInit` is `Rinit`'s own `gamma`, which `zonotope(Rinit)` uses, and
`gamma` is `options.gamma`. `options.Rhom` is passed on as a set, as `post` carries it: the
covariance `enclose` gives it stays in `Rfirst.ti`, `0` for a deterministic `Rinit`.

## References

* [1] `contDynamics/@linProbSys/initReach.m`, `private/priv_pexpm.m`, `private/priv_tie.m`,
      `private/priv_inputSolution.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[Rfirst, options] = initReach(obj, Rinit, params, options)`, line by line, the input
covariance's sign corrected. -/
noncomputable def LinProbSys.initReach (sys : LinProbSys n m) (Veig : Mat ℝ n n)
    (lambda : Fin n → ℝ) (Rinit : ProbZonotope n) (gammaInit : ℝ) (U : Zonotope (Vec ℝ m))
    (uTrans : Vec ℝ m) (r : ℝ) (η : ℕ) (gamma : ℝ) (originContained : Bool) :
    ProbZonotope n × ProbZonotope n × LinProbSys.PostState n × ProbZonotope n :=
  let A := sys.A
  -- priv_pexpm, priv_tie
  let eAt := NormedSpace.exp (r • A)                                -- obj.taylor.eAt
  let F := MatExp.correctionMatrix A r η                            -- obj.taylor.F
  -- priv_inputSolution, non-probabilistic solution
  let V := Zonotope.mtimes sys.B U                                  -- V = obj.B*params.U
  let vTrans := sys.B *ᵥ uTrans                                     -- vTrans = obj.B*params.uTrans
  let inputSolV := (⟨A⟩ : LinearSys ℝ n).inputSolution (S := 𝒵) r η V   -- Vsum+E*r*V
  let inputSolVtrans := (A⁻¹ * (eAt - 1)) *ᵥ vTrans                -- inv(A)*(expm(A*r)-I)*vTrans
  let inputCorr : Zonotope (Vec ℝ n) := if originContained then Zonotope.ofPoint 0
    else Zonotope.mtimesIntervalMat (Interval.matMul (Interval.point A⁻¹) F)
      (Zonotope.ofPoint vTrans)                                     -- inv(A)*F*zonotope(vTrans)
  let uncertainMean := inputSolV.plus (Zonotope.ofPoint inputSolVtrans)
  let Rinput : ProbZonotope n := ⟨uncertainMean, 0⟩                -- probZonotope([c,G],0,gamma)
  let Rtrans := inputSolVtrans
  -- priv_inputSolution, probabilistic solution
  let Sigma := LinProbSys.inputCov Veig lambda sys.C r             -- Sigma=V*Sigma*V.', corrected
  let pRinput : ProbZonotope n := ⟨Zonotope.ofPoint 0, Sigma⟩      -- probZonotope(0,G,gamma)
  -- initReach
  let Rhom_tp := ProbZonotope.mtimes eAt Rinit                      -- Rhom_tp=eAt*Rinit
  let Raux := Rinit.enclose (r • A) gammaInit Rtrans                -- enclose(Rinit,A*r,Rtrans)
  let Rhom := ProbZonotope.plus (ProbZonotope.plus (ProbZonotope.plus Raux
    ⟨Zonotope.mtimesIntervalMat F (Rinit.zonotope gammaInit), 0⟩) ⟨inputCorr, 0⟩)
    ⟨Zonotope.ofPoint (-Rtrans), 0⟩                    -- Raux+F*zonotope(Rinit)+inputCorr+(-Rtrans)
  let Rpar := ProbZonotope.plus Rinput pRinput                      -- Rpar=Rinput+pRinput
  let Rtotal := ProbZonotope.plus Rhom ⟨Rpar.zonotope gamma, 0⟩     -- Rhom+zonotope(Rpar)
  let Rtotal_tp := ProbZonotope.plus Rhom_tp ⟨Rpar.zonotope gamma, 0⟩  -- Rhom_tp+zonotope(Rpar)
  let RauxDet := Rinput.zonotope 0                                 -- zonotope(Rinput,0)
  let Rpar_det := RauxDet.interval                                 -- interval(RauxDet)
  let Rpar_prob : ProbZonotope n := ⟨pRinput.zonotope gamma, 0⟩    -- zonotope(pRinput)
  (Rtotal_tp, Rtotal, ⟨Rhom.Z, Rpar_det, Rpar_prob, RauxDet⟩, pRinput)  -- Rhom.Z

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
