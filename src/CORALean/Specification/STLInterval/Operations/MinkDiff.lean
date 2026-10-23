module

public import CORALean.Global.Float.TimeOrder
public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minkDiff`: Minkowski difference of two STL intervals

`@stlInterval/minkDiff.m` (type `'exact'`; `'inner'` computes the same): `I1 - I2 = I` with
`I + I2 ⊆ I1`. An empty `I2` gives `[0, ∞)`, an empty `I1` the empty interval. CORA's
`ub = obj.upper - sub.upper` is `Inf - Inf = NaN` for two unbounded operands; here that case is
`+∞`, the Minkowski difference (see `STLInterval.minkDiffCora`). Over a float scalar the lower bound
is rounded down and the upper one up, so the result encloses the exact one.

## Inputs
* none

## Output
* the Minkowski difference of the two intervals
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def STLInterval.minkDiff : STLInterval 𝕋 → STLInterval 𝕋 → STLInterval 𝕋
  | _, .empty => stlInterval 0 ⊤ true false toReal_zero_eq.ge
  | .empty, _ => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let lc := lc₁ || !lc₂
    let rc := rc₁ || !rc₂
    match u₁, u₂ with
    -- `upper - inf` is `-inf`: nothing is left
    | some _, none => .empty
    | _, _ =>
      -- `lower - lower'` rounded down to `upper - upper'` rounded up, `inf` if `upper` is
      let lb := subDown l₁ l₂
      let ub := subUpTop u₁ u₂
      if h : toReal lb < toReal (0 : 𝕋) then stlInterval 0 ub true rc toReal_zero_eq.ge
      else stlInterval lb ub lc rc (by rw [← toReal_zero_eq (𝕋 := 𝕋)]; exact not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
