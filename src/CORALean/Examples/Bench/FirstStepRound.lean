import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Examples.Bench.Config
import CORALean.Examples.Bench.Rational

/-!
# `firststep`: `X0` rounded outward into a number type

`firststep` takes `X0 = c + Σ_j β_j g_j` from the config exactly, which a format may not hold.
`roundX0In` stores `c' = ⌊c⌋`, `g'_j = ⌊g_j⌋` and puts what the rounding lost into the error box
`E`: `E = [-W, W + w_c]` with `W = Σ_j w_{g_j}`, summed over `j` and rounded up. The set so stored
contains the exact `X0`. Where the config's numbers are on the grid every width is zero and `E` is
the point `0`, the set `Rollout.buildX0` gives. `⌊x⌋`/`⌈x⌉` are `addDown x 0`/`addUp x 0` applied
to `exactIn x`, so the format's own rounded operation does the rounding.

## Inputs
* `cfg` – headline config
* `exactIn` – exact number held off the grid

## Output
* initial zonotope rounded outward or an error
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `⌊x⌋` and `⌈x⌉` of the exact value `exactIn d`, in the format. -/
def aux_downUp (exactIn : ExactDyadic → 𝕋) (d : String) : Except String (𝕋 × 𝕋) := do
  let x := exactIn (← parseExact d)
  pure (FloatOps.addDown x FloatOps.zero, FloatOps.addUp x FloatOps.zero)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The config's `X0`, rounded outward as the module docstring says. -/
def roundX0In (cfg : HeadlineConfig) (exactIn : ExactDyadic → 𝕋) :
    Except String (Zonotope (Vec 𝕋 2)) := do
  if cfg.x0Center.size ≠ 2 then throw "config `x0.center` must have exactly 2 entries"
  for row in cfg.x0Generators do
    if row.size ≠ 2 then throw "config `x0.generators` rows must each have exactly 2 entries"
  let c ← cfg.x0Center.mapM (aux_downUp exactIn)
  let g ← cfg.x0Generators.mapM (·.mapM (aux_downUp exactIn))
  let z : 𝕋 := FloatOps.zero
  let gAt (i j : ℕ) : 𝕋 × 𝕋 := ((g.getD j #[]).getD i (z, z))
  let cAt (i : ℕ) : 𝕋 × 𝕋 := c.getD i (z, z)
  let w (i : Fin 2) : 𝕋 := sumUp fun j : Fin cfg.x0Generators.size =>
    subUp (gAt i j).2 (gAt i j).1
  pure
    { h := cfg.x0Generators.size
      c := fun i => (cAt i).1
      G := fun j i => (gAt i j).1
      I_error := ⟨-w,
            fun i => FloatOps.addUp (w i) (subUp (cAt i).2 (cAt i).1)⟩ }

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
