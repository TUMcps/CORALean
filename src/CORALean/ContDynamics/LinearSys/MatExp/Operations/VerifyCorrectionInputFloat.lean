module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrConvergedFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrSumsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `MatExp.verifyCorrectionInputFloat`, the `G` of CORA's `priv_verifyRA_supportFunc`, made sound

CORA's `aux_intmat` sums the input correction matrix `G` alongside `F`: the term of `η` is
`[κ_η r^η / η, 0] A^{η-1}/(η-1)!` (`factor * Apower{η-1} / η`), the stopping rule and the limit
`74` are `F`'s. Here the coefficient is `corrCoeffLowTight` divided by `η` (from below:
`max 1 (nsmulDown η 1)`), the powers are `verifyPowerFloat`, the sums are accumulated outward from
the first term up, and the tail past the `η - 2` terms is `r` times the scaled remainder at order
`η - 2`, so `G` encloses the input correction for every member. As for `F`, the search starts at
`η = 3`. `none` where no `η ≤ 74` passes or the remainder is not admissible.

## Inputs
* `A` – float system matrix
* `s` – positive float scales of the remainder
* `r` – float step length

## Output
* the order `η` at which the sums stopped and the interval matrix `G`, none if not converged
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The term of `η = i + 2`: `[κ_η r^η / η, 0] A^{η-1}/(η-1)!` (CORA's `factor*Apower{η-1}/η`). -/
@[step_of MatExp.verifyCorrectionInputFloat]
def MatExp.step_verifyConstCorrTermFloat (A : Mat 𝕋 n n) (r : 𝕋) (i : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let c := mulDown (MatExp.corrCoeffLowTight (i + 2)) (MatExp.powUp (i + 2) r)  -- κ r^η ≤ 0
  let cLo := divDown c (maximum one (nsmulDown (i + 2) one))                    -- / η
  Interval.smul cLo zero (MatExp.verifyPowerFloat A (i + 1))                    -- [cLo, 0] P


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `G` at the first `η ∈ [3, 74]` whose term no longer changes the sums of the `η - 2` terms
before it, those sums widened by `r` times the scaled remainder at `η - 2`. -/
def MatExp.verifyCorrectionInputFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (r : 𝕋) :
    Option (ℕ × Interval (Mat 𝕋 n n)) := do
  let T := fun i => MatExp.step_verifyConstCorrTermFloat A r i               -- the terms
  let S := fun η => MatExp.verifyCorrSumsFloat                              -- terms 0 … η-3
    ((List.range (η - 2)).map T)
  let η ← (List.range' 3 72).find? fun η =>                                  -- the first stop
    MatExp.verifyCorrConvergedFloat (S η) (T (η - 2))
  let W ← MatExp.scaledRemainderFloat A s r (η - 2)                          -- E(r, η-2)
  let Sη := S η                                                              -- the sums kept
  let G : Interval (Mat 𝕋 n n) :=
    ⟨fun j k => subDown (Sη.inf j k) (mulUp r (W j k)),
      fun j k => addUp (Sη.sup j k) (mulUp r (W j k))⟩
  pure (η, G.materialiseMat)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
