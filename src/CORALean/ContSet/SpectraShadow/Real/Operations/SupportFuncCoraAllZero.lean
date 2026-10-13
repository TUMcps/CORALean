module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

@[expose] public section

/-!
# `SpectraShadow.supportFuncCoraAllZero`

The `'upper'` value CORA's `@spectraShadow/supportFunc_` returns when every `Aᵢ` is zero
(`all_Ai_zero`): `+Inf` if `A₀ ⪰ 0` (`eig(A0) >= 0`), `-Inf` otherwise, whatever `G` and `c`
are. With every `Aᵢ` zero the inequality does not involve `β`, so the set is `c + range G` or
empty, and the support in direction `d` is `dᵀc` when `dᵀG = 0`, in particular for `G = 0`.
Formalized as the code computes it, to state the counterexample
`SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`; see `FINDINGS.md`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The `'upper'` value of the `all_Ai_zero` branch. -/
noncomputable def SpectraShadow.supportFuncCoraAllZero (S : SpectraShadow α) : EReal :=
  if S.A₀.PosSemidef then ⊤ else ⊥

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
