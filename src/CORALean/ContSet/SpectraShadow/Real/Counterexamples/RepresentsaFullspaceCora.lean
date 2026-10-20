module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleNotMem
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqTopOfUnbounded

@[expose] public section

/-!
# `SpectraShadow.representsa_fullspaceCora`

CORA's test for `'fullspace'` in `@spectraShadow/representsa_`,
`representsa_(interval(SpS), 'fullspace')`: every coordinate range is the whole line, that is
every axis support in both directions is `Inf`. A line in the plane passes. Formalized as the
code computes it, to state the counterexample `SpectraShadow.representsa_fullspaceCora_line`;
see `references/coverage/contSet/spectraShadow.md`, row `representsa_`.

# `SpectraShadow.representsa_fullspaceCora_line`

`representsa_` at `'fullspace'`: every axis support of the line `{(t, t)}` is infinite, so CORA's
`interval(SpS)` is the whole plane and it answers `true`, but the line is not the plane. Read from
the source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's `'fullspace'` test accepts the line `{(t, t)}`, which is not the plane
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- Every axis support, in both directions, is infinite. -/
noncomputable def SpectraShadow.representsa_fullspaceCora (S : SpectraShadow (Vec ℝ n)) : Prop :=
  ∀ i : Fin n, S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) = ⊤
    ∧ S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) = ⊤

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.representsa_fullspaceCora_line :
    SpectraShadow.lineExample.representsa_fullspaceCora
      ∧ SpectraShadow.lineExample.construct ≠ Set.univ := by -- --- PROOF ---
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · -- the diagonal point `|M| + 1` exceeds any bound `M`
    refine SpectraShadow.lineExample.supportFunc_eq_top_of_unbounded _ fun M => ?_
    exact ⟨fun _ => |M| + 1, SpectraShadow.lineExample_mem _, by
      simp; linarith [le_abs_self M, neg_abs_le M]⟩
  · -- and its negative, in the other direction
    refine SpectraShadow.lineExample.supportFunc_eq_top_of_unbounded _ fun M => ?_
    exact ⟨fun _ => -(|M| + 1), SpectraShadow.lineExample_mem _, by
      simp; linarith [le_abs_self M, neg_abs_le M]⟩
  · -- `(1, 0)` is not on the diagonal
    intro h
    have : (Pi.single 0 1 : Vec ℝ 2) ∈ SpectraShadow.lineExample.construct := by
      rw [h]; trivial
    obtain ⟨β, -, hx⟩ := this
    exact SpectraShadow.lineExample_not_mem ⟨β, hx.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
