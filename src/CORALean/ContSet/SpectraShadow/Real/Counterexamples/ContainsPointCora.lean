module

public import CORALean.ContSet.SpectraShadow.Real.Operations.ContainsPoint
public import CORALean.ContSet.SpectraShadow.Real.Theorems.LineExampleNotMem

@[expose] public section

/-!
# `SpectraShadow.containsPointCora`

What CORA's `aux_containsPoint` answers: when the solver reports the program infeasible
(status `1`) it sets `t = 0` and answers `true`, on the stated ground that the problem cannot be
infeasible. It can: `c + G β = p` has no solution for `p` outside `c + range G`. Formalized as the
code computes it, to state `SpectraShadow.containsPointCora_line`; see
`references/coverage/contSet/spectraShadow.md`, row `contains_`.

# `SpectraShadow.containsPointCora_line`

`contains_` on a numeric operand: `(1, 0)` is not on the line `{(t, t)}`, so `c + G β = p` is
infeasible and CORA, reading the solver's status `1` as an internal error, answers `true`. Read from
the source, not run.

## Inputs
* `tol` – tolerance

## Hypotheses
* none

## Conclusion
* CORA answers `true` for `(1, 0)` against the line `{(t, t)}`, which excludes it
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
/-- What CORA answers: `true` also when no `β` reaches `p` (the solver's `problem == 1`). -/
def SpectraShadow.containsPointCora (S : SpectraShadow α) (p : α) (tol : ℝ) : Prop :=
  (¬ ∃ β : Fin S.m → ℝ, S.c + ∑ i, β i • S.G i = p) ∨ S.containsPoint p tol

end CORALean.Real

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.containsPointCora_line (tol : ℝ) :
    SpectraShadow.lineExample.containsPointCora (Pi.single 0 1) tol
      ∧ (Pi.single 0 1 : Vec ℝ 2) ∉ SpectraShadow.lineExample.construct := by
  refine ⟨Or.inl SpectraShadow.lineExample_not_mem, ?_⟩
  rintro ⟨β, -, hx⟩
  exact SpectraShadow.lineExample_not_mem ⟨β, hx.symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
