module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyTimeSetdiff
public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopePassFloat
public import CORALean.ContDynamics.LinearSys.Operations.VerifyZonotopeWitnessFloat

@[expose] public section

/-!
# `LinearSys.verifyZonotopeRunFloat`, CORA's `priv_verifyRA_zonotope` over its passes

CORA refines its passes until every specification holds on `[0, t_f]` or one is falsified. Here
the passes' grids are given (CORA's tuning, not checked). Each specification keeps its
unverified times, `[0, t_f]` at the start; a step whose output set holds it removes the step's
interval (`LinearSys.verifyTimeSetdiff`). The run is verified when no time is left for any
specification, and falsified when a witness, an initial point and an input held constant, is
checked to violate one at a time within `t_f` (`LinearSys.verifyZonotopeWitnessFloat`). Otherwise
it is undecided (`none`). A pass that is not computed removes nothing.

## Inputs
* `A` – float system matrix
* `c` – float center of the initial set
* `G` – float generators of the initial set
* `Bm` – float input matrix
* `uc` – float center of the input set
* `GU` – float generators of the input set
* `C` – float output matrix
* `specs` – float safe and unsafe sets in the output space
* `passes` – the grids of the passes, from CORA's tuning
* `witnesses` – candidate falsifications: a specification's index, a time, `b` and `β`
* `tFinal` – horizon

## Output
* `some true` verified, `some false` falsified, `none` undecided
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m k p q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The intervals of a pass on which `S` holds, its steps from `t₀`. -/
@[step_of LinearSys.verifyZonotopeRunFloat]
def LinearSys.step_verifyRunTimesFloat (S : LinearSys.VerifySpecSet 𝕋 q) :
    List (LinearSys.VerifyGridStep 𝕋) → List (Option (LinearSys.VerifyZono 𝕋 q × List Bool)) →
      ℚ → List (ℚ × ℚ)
  | g :: gs, o :: os, t₀ =>
    let t₁ := t₀ + ToRat.toRat g.Δt
    (match o with
      | some (Y, _) => if LinearSys.verifySpecHoldsFloat Y S then [(t₀, t₁)] else []
      | none => []) ++ LinearSys.step_verifyRunTimesFloat S gs os t₁
  | _, _, _ => []


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The passes, the times left per specification, the witnesses: verified, falsified or
undecided. -/
def LinearSys.verifyZonotopeRunFloat (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (G : Mat 𝕋 n m)
    (Bm : Mat 𝕋 n k) (uc : Vec 𝕋 k) (GU : Mat 𝕋 k p) (C : Mat 𝕋 q n)
    (specs : List (LinearSys.VerifySpecSet 𝕋 q)) (passes : List (List (LinearSys.VerifyGridStep 𝕋)))
    (witnesses : List (ℕ × 𝕋 × Vec 𝕋 m × Vec 𝕋 p)) (tFinal : 𝕋) : Option Bool :=
  let outs := passes.filterMap fun grid =>                               -- the computed passes
    (LinearSys.verifyZonotopePassFloat A c G Bm uc GU C specs grid).map (grid, ·)
  let unverified := fun S => (outs.flatMap fun go =>                     -- the times left for `S`
    LinearSys.step_verifyRunTimesFloat S go.1 go.2 0).foldl
      (fun U iv => LinearSys.verifyTimeSetdiff U iv.1 iv.2) [(0, ToRat.toRat tFinal)]
  let falsified := witnesses.any fun w => match specs[w.1]? with
    | some S => le w.2.1 tFinal &&
      LinearSys.verifyZonotopeWitnessFloat A c G Bm uc GU C S w.2.1 w.2.2.1 w.2.2.2
    | none => false
  if falsified then some false
  else if specs.all fun S => (unverified S).isEmpty then some true
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
