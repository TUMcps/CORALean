module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.containsPoint`

CORA's `@spectraShadow/contains_` on a numeric operand (`aux_containsPoint`): for the point `p`
it solves `min t` subject to `A₀ + Σ βᵢ Aᵢ + diag(s) ⪰ 0`, `c + G β = p` and `|sᵢ| ≤ t`, and
answers `t ≤ tol`. That has a solution exactly when some `β` and some slack `s` of size at most
`tol` give a positive semidefinite matrix. At `tol = 0` the slack is zero and the test is
membership; for `tol > 0` it admits points slightly outside, which is why CORA has the slack.
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

/-- Some `β` reaches `p` and some slack of size `≤ tol` makes the inequality hold. -/
def SpectraShadow.containsPoint (S : SpectraShadow α) (p : α) (tol : ℝ) : Prop :=
  ∃ (β : Fin S.m → ℝ) (s : Fin S.k → ℝ), S.c + ∑ i, β i • S.G i = p ∧ (∀ i, |s i| ≤ tol)
    ∧ (S.A₀ + ∑ i, β i • S.A i + Matrix.diagonal s).PosSemidef

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
