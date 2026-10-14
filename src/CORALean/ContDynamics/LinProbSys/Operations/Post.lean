module

public import CORALean.ContDynamics.LinProbSys.Definitions.PostState
public import CORALean.ContDynamics.LinProbSys.LinProbSys
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.ProbZonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

/-!
# One step of the probabilistic reach loop

CORA's `linProbSys/post` [1]: every set is carried by `e^{AΔt}`, the box of the deterministic
particular solution grows by the box of `RauxDet`, the probabilistic one by `pRinput`, the
input solution of one step that `initReach` computes (an argument here), and the time-interval
set is `Rhom + Rpar_prob + zonotope(Rpar_det)`, a probabilistic zonotope. `Rnext.tp` is `[]`.

## References

* [1] `contDynamics/@linProbSys/post.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[Rnext, options] = post(obj, R, params, options)`, line by line. -/
noncomputable def LinProbSys.post (sys : LinProbSys n m) (Δt : ℝ) (pRinput : ProbZonotope n)
    (st : LinProbSys.PostState n) : LinProbSys.PostState n × ProbZonotope n :=
  let eAt := NormedSpace.exp (Δt • sys.A)                            -- obj.taylor.eAt
  let Rhom := Zonotope.mtimes eAt st.Rhom                            -- Rhom = eAt*Rhom
  let Rpar_det := Interval.plus st.Rpar_det st.RauxDet.interval     -- Rpar_det + interval(Raux_det)
  let Rpar_prob := ProbZonotope.plus (ProbZonotope.mtimes eAt st.Rpar_prob) pRinput
  let RauxDet := Zonotope.mtimes eAt st.RauxDet                      -- Raux_det = eAt*Raux_det
  let Rti := ProbZonotope.plus (ProbZonotope.plus ⟨Rhom, 0⟩ Rpar_prob)
    ⟨Rpar_det.zonotope, 0⟩                                      -- Rhom+Rpar_prob+zonotope(Rpar_det)
  (⟨Rhom, Rpar_det, Rpar_prob, RauxDet⟩, Rti)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
