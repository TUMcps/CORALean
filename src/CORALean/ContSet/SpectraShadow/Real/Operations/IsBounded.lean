module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

@[expose] public section

/-!
# `SpectraShadow.isBounded`

CORA's `@spectraShadow/isBounded`: for every coordinate `i`, the upper support function in `eᵢ`
and in `-eᵢ` is not `Inf` (a semidefinite program each). The emptiness shortcut (`isemptyobject`,
a MATLAB object test) is not modelled: the empty set has support `-Inf` and passes the loop.

CORA's `supportFunc_` returns `Inf` whenever every `Aᵢ` is zero and `A₀ ⪰ 0`, whatever `G` is
(`SpectraShadow.supportFuncCoraAllZero`), so CORA calls the point `{c}` of `G = 0` unbounded;
`isBounded` here is the loop over the true support values. See
`references/coverage/contSet/spectraShadow.md`, row `isBounded`.

## Inputs
* `S` – spectrahedral shadow

## Output
* the loop of CORA's `isBounded`: both upper supports along every axis are finite
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop of CORA's `isBounded`: both upper supports along every axis are finite. -/
noncomputable def SpectraShadow.isBounded (S : SpectraShadow (Vec ℝ n)) : Prop :=
  ∀ i : Fin n, S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) ≠ ⊤
    ∧ S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) ≠ ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
