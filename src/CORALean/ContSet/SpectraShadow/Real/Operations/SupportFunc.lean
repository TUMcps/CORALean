module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `SpectraShadow.supportFunc`

CORA's `@spectraShadow/supportFunc_` solves the semidefinite program `min ∓ dᵀ G β` subject to
`A₀ + Σ βᵢ Aᵢ ⪰ 0` and returns `dᵀ(c + G β)`, `+∞` when it is unbounded and `-∞` when it is
infeasible. `supportFunc` is the value that program has, the supremum of the functional over the
set, in `EReal`: `⊥` for the empty set, `⊤` for an unbounded direction. A specification, not
computed, as the program is not; `SpectraShadow.supportBound` is the certified bound.
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

/-- The supremum of `c` over the set, `⊥` if it is empty and `⊤` if `c` is unbounded on it. -/
noncomputable def SpectraShadow.supportFunc (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) : EReal :=
  ⨆ x ∈ S.construct, ((c x : ℝ) : EReal)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
