module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
public import CORALean.ContSet.SpectraShadow.Real.Theorems.PointExampleConstruct

@[expose] public section

/-!
# `SpectraShadow.supportFuncCoraAllZero`

The `'upper'` value CORA's `@spectraShadow/supportFunc_` returns when every `Aᵢ` is zero
(`all_Ai_zero`): `+Inf` if `A₀ ⪰ 0` (`eig(A0) >= 0`), `-Inf` otherwise, whatever `G` and `c`
are. With every `Aᵢ` zero the inequality does not involve `β`, so the set is `c + range G` or
empty, and the support in direction `d` is `dᵀc` when `dᵀG = 0`, in particular for `G = 0`.
Formalized as the code computes it, to state the counterexample
`SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`; see
`references/coverage/contSet/spectraShadow.md`, row `supportFunc_`.

# `SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`

`supportFunc_` and `isBounded` on the point `{0}` (`A₀ = 1`, `A₁ = 0`, `G = 0`): CORA's
`all_Ai_zero` branch returns `+Inf` while the support is `0`. Read from the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `+Inf` support of the point `{0}` differs from its true support
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- The `'upper'` value of the `all_Ai_zero` branch. -/
noncomputable def SpectraShadow.supportFuncCoraAllZero (S : SpectraShadow α) : EReal :=
  if S.A₀.PosSemidef then ⊤ else ⊥

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.supportFuncCoraAllZero_ne_supportFunc :
    SpectraShadow.pointExample.supportFuncCoraAllZero
      ≠ SpectraShadow.pointExample.supportFunc
        (LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ) := by -- --- PROOF ---
  -- CORA: `A₀ = 1 ⪰ 0`, so `+Inf`
  have h1 : SpectraShadow.pointExample.supportFuncCoraAllZero = ⊤ := by
    classical
    simp only [SpectraShadow.supportFuncCoraAllZero, SpectraShadow.pointExample]
    rw [if_pos Matrix.PosSemidef.one]
  -- the set: the support in the one coordinate is `0`
  have h2 : SpectraShadow.pointExample.supportFunc
      (LinearMap.proj 0 : Vec ℝ 1 →ₗ[ℝ] ℝ) = 0 := by
    rw [SpectraShadow.supportFunc, SpectraShadow.pointExample_construct]
    simp
  rw [h1, h2]
  exact EReal.top_ne_zero

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
