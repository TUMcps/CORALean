module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrCoeffLowTightFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrConvergedFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.VerifyCorrSumsFloat

@[expose] public section

/-!
# `MatExp.verifyCorrectionStateFloat`, the `F` of CORA's `priv_verifyRA_supportFunc`, made sound

CORA's `aux_intmat` sums the terms `[κᵢ rⁱ, 0] Aⁱ/i!` of the state correction matrix `F` from
`i = 2` and stops at the first `η` whose term no longer changes the sums (`eps` times the upper
sum above its upper end, `eps` times the lower sum below its lower end); past `η = 74` the step
counts as not converged. The sums before that term are CORA's `F`, with no remainder. Here the
coefficient is `corrCoeffLowTight`, the powers are `verifyPowerFloat`, the sums are rounded
outward from `i = 2` up, and the tail past order `η - 1` is `scaledRemainderFloat`, so `F`
encloses the correction for every member. The search starts at `η = 3`, where the remainder has
an order of at least `2`; CORA would stop at `η = 2` only for `A² = 0`.

## Inputs
* `A` – float system matrix
* `s` – positive float scales of the remainder
* `r` – float step length

## Output
* the order `η` at which the sums stopped and the interval matrix `F`, none if not converged
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

/-- The term `[κᵢ rⁱ, 0] Aⁱ/i!` of order `i` (CORA's `factor * Apower{i}`, split by sign). -/
@[step_of MatExp.verifyCorrectionStateFloat]
def MatExp.step_verifyCorrTermFloat (A : Mat 𝕋 n n) (r : 𝕋) (i : ℕ) : Interval (Mat 𝕋 n n) :=
  let cLo := mulDown (MatExp.corrCoeffLowTight i) (MatExp.powUp i r)        -- κᵢ rⁱ ≤ 0
  Interval.smul cLo zero (MatExp.verifyPowerFloat A i)                       -- [κᵢ rⁱ, 0] Aⁱ/i!


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `F` at the first `η ∈ [3, 74]` whose term no longer changes the sums of the orders `2` to
`η - 1`, those sums widened by the scaled remainder at `η - 1`. -/
def MatExp.verifyCorrectionStateFloat (A : Mat 𝕋 n n) (s : Vec 𝕋 n) (r : 𝕋) :
    Option (ℕ × Interval (Mat 𝕋 n n)) := do
  let T := fun i => MatExp.step_verifyCorrTermFloat A r i                    -- the terms
  let S := fun η => MatExp.verifyCorrSumsFloat                              -- orders 2 … η-1
    ((List.range (η - 2)).map fun i => T (i + 2))
  let η ← (List.range' 3 72).find? fun η =>                                  -- the first stop
    MatExp.verifyCorrConvergedFloat (S η) (T η)
  let W ← MatExp.scaledRemainderFloat A s r (η - 1)                          -- E(r, η-1)
  let Sη := S η                                                              -- the sums kept
  let F : Interval (Mat 𝕋 n n) :=
    ⟨fun j k => subDown (Sη.inf j k) (W j k), fun j k => addUp (Sη.sup j k) (W j k)⟩
  pure (η, F.materialiseMat)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
