import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.Examples.Bench.Rollout
import CORALean.ContDynamics.LinearSys.Operations.CanonicalFloat

/-!
# The spiral system at continuous time, for `headline-a`/`headline-b`

Where `Rollout.buildSystem` discretizes `A` by a first-order Euler step for
`dtdemo`'s placeholder, `buildContSystem` reads `A = [[a, b], [-b, a]]` itself
into `𝕋`, exactly, through the checked `inst` (config values are exact at 2
bits, so this never rejects a config that also fits `X0`). `LinearSys.reachWrappingFreeFloat`,
`.reachFloat` and `.reachTimePointWrappingFreeFloat` take `A` this way, unlike
`LinearSysDT.reach`, which needs the discretized matrix `buildSystem` builds.

## Inputs
* `cfg` – headline config
* `inst` – checked reader of exact numbers

## Output
* continuous-time spiral system and initial zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `⟨A⟩` and `X0` read exactly into `𝕋` from the config's `a`, `b` and
`x0` -- the continuous-time counterpart of `Rollout.buildSystem`. -/
def buildContSystem (cfg : HeadlineConfig) (inst : String → ExactDyadic → Except String 𝕋) :
    Except String (LinearSys 𝕋 2 × Zonotope (Vec 𝕋 2)) := do
  let a ← inst "system.a" (← parseExact cfg.a)
  let b ← inst "system.b" (← parseExact cfg.b)
  let nb ← inst "system.b" (← parseExact cfg.b).neg
  let z0 ← inst "0" ExactDyadic.zero
  let X0 ← buildX0 cfg inst z0
  let A : Mat 𝕋 2 2 := Matrix.of ![![a, b], ![nb, a]]
  pure (LinearSys.canonicalFloat A, X0)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
