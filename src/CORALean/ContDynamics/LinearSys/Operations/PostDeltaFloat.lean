import CORALean.ContDynamics.LinearSys.Operations.DeltaReachFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat

/-!
# `postΔ` in floats

`postDelta` computed in `𝕋`, [1, Sec. 4.1]'s `R∆(τs) = post∆(R(ts), Ψ(τs), A)` and
CORA's `Rdelta = Rhom + RV`: `deltaReachFloat` for the homogeneous part, and for the
input set `V` what it contributes up to any time of the step. `V` is split at its
stored centre as `reachFloatInput` splits it, so `0 ∈ V` is not asked: the
constant `ũ` contributes `inputSolutionFloat` of the segment `[0, ũ]`, the rest
`Ũ = V - ũ ∋ 0` its own `inputSolutionFloat`, each covering every time up to `Δt`.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state difference a step can span from `R` under inputs in `V`:
`deltaReachFloat R ⊕ P̃^R([0, ũ]) ⊕ P^R(V - ũ)` at Taylor order `η`. -/
def LinearSys.postDeltaFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) (R V : Zonotope (Vec 𝕋 n)) :
    Zonotope (Vec 𝕋 n) :=
  let ũ := (Interval.point V.c).zonotope                            -- {ũ}, V's stored centre
  let Ũ := Recentre.recentre V                                      -- Ũ = V - ũ, holding 0
  let seg := LinComb.linComb (Interval.point fun _ => zero).zonotope ũ    -- [0, ũ]
  sys.deltaReachFloat Δt η R ⊞                                      -- Rhom
    (sys.inputSolutionFloat Δt η seg ⊞ sys.inputSolutionFloat Δt η Ũ)    -- RV

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
