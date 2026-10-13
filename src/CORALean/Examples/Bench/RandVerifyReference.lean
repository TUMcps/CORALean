import CORALean.Examples.Bench.RandVerifyInstance
import CORALean.Examples.Bench.RandVerifyOutExact
import CORALean.Examples.Bench.RandVerifyReach
import CORALean.Examples.Bench.RandVerifyRead
import CORALean.Global.Float.Instances.Dyadic.API

/-!
# `randverify-family`: the reference windows

The windows of the instance's system in output space, `Y_k = C · R(τ_k)` exactly over ℚ
(`outputZonoExact`), with `R(τ_k)` from the wrapping-free reach with inputs at `Dyadic p`, step
`dt`, Taylor order `η` and zonotope order `ρ`. The reach is sound, so each `Y_k` contains the
output of every trajectory over its time interval: a box beyond every `Y_k` along a direction is
beyond the true reachable set by at least as much.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float


-- =====================================  MAIN DEFINITION  ====================================== --

def referenceWindows (I : RandInstance) (p : ℕ) (dt : ℚ) (η ρ : ℕ) :
    Except String (List RandOutZono) := do
  let S ← readRandSystem (𝕋 := Dyadic p) (fun field d => d.toDyadicP field p)
    ExactDyadic.toDyadicPUnchecked I dt
  if S.x0Enclosed then throw s!"X0 is not exact at Dyadic {p}"
  let Rs ← randVerifyReach .wrappingFree S I.tend η ρ
  pure (Rs.map (outputZonoExact I.C))

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
