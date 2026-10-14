module

public import CORALean.Specification.STLInterval.Operations.StlInterval
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# `minkDiff`, as printed

`@stlInterval/minkDiff.m` with `ub = obj.upper - sub.upper` as MATLAB computes it: `Inf - Inf` is
`NaN`, which the constructor `stlInterval(lb,ub,lc,rc)` keeps (`abs(NaN) == inf`, `lb > NaN` and
`lb == NaN` are false), so for two unbounded operands the object has `upper = NaN`. Elsewhere the
result is that of `STLInterval.minkDiff`. See `STLInterval.minkDiffCora_counterexample`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.minkDiffCora : STLInterval → STLInterval → Option STLInterval.Fields
  | _, .empty => fieldsOf (stlInterval 0 ⊤ true false)
  | .empty, _ => none
  | .nonempty l₁ u₁ lc₁ rc₁ _ _ _, .nonempty l₂ u₂ lc₂ rc₂ _ _ _ =>
    let lb := l₁ - l₂
    let ub : Option EReal := if u₁ = ⊤ ∧ u₂ = ⊤ then none else some (u₁ - u₂)
    let lc := lc₁ || !lc₂
    let rc := rc₁ || !rc₂
    match ub with
    | none => if lb < 0 then some ⟨0, none, true, rc⟩ else some ⟨lb, none, lc, rc⟩
    | some ub => if lb < 0 then fieldsOf (stlInterval 0 ub true rc)
      else fieldsOf (stlInterval lb ub lc rc)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
