module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

@[expose] public section

/-!
# `SpectraShadow.representsa_fullspaceCora`

CORA's test for `'fullspace'` in `@spectraShadow/representsa_`,
`representsa_(interval(SpS), 'fullspace')`: every coordinate range is the whole line, that is
every axis support in both directions is `Inf`. A line in the plane passes. Formalized as the
code computes it, to state the counterexample `SpectraShadow.representsa_fullspaceCora_line`;
see `FINDINGS.md`.
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

/-- Every axis support, in both directions, is infinite. -/
noncomputable def SpectraShadow.representsa_fullspaceCora (S : SpectraShadow (Vec ℝ n)) : Prop :=
  ∀ i : Fin n, S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) = ⊤
    ∧ S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) = ⊤

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
