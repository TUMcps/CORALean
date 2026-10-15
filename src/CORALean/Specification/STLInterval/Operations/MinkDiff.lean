module

public import CORALean.Specification.STLInterval.Operations.StlInterval

@[expose] public section

/-!
# `minkDiff`: Minkowski difference of two STL intervals

`@stlInterval/minkDiff.m` (type `'exact'`; `'inner'` computes the same): `I1 - I2 = I` with
`I + I2 ⊆ I1`. An empty `I2` gives `[0, ∞)`, an empty `I1` the empty interval. CORA's
`ub = obj.upper - sub.upper` is `Inf - Inf = NaN` for two unbounded operands; here that case is
`+∞`, the Minkowski difference (see `STLInterval.minkDiffCora`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.minkDiff : STLInterval → STLInterval → STLInterval
  | _, .empty => stlInterval 0 ⊤ true false le_rfl
  | .empty, _ => .empty
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ _ =>
    let lb := l₁ - l₂
    let ub := if u₁ = ⊤ ∧ u₂ = ⊤ then ⊤ else u₁ - u₂
    let lc := lc₁ || !lc₂
    let rc := rc₁ || !rc₂
    if h : lb < 0 then stlInterval 0 ub true rc le_rfl else stlInterval lb ub lc rc (not_lt.1 h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
