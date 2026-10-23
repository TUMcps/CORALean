module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# `HPolytope.boundOfDual`

A halfspace description *is* an LP feasible set, so weak duality applies to it
directly: a nonnegative weighting of its own rows bounds whatever objective the
weighting assembles.

## Inputs
* `P` – H-polytope
* `c` – linear functional
* `y` – real numbers indexed by `Fin P.m`
* `z` – real numbers indexed by `Fin P.me`

## Hypotheses
* `hy` – `∀ i, 0 ≤ y i`
* `hc` – `c` is the combination of the rows with weights `y`, `z`

## Output
* a support bound in direction `c`, from the dual weights `y`, `zu`, `zl`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `hc` is dual feasibility, `c = yᵀA + zᵀAe`, stated pointwise because a
functional is determined by what it does. -/
def HPolytope.boundOfDual (P : HPolytope α) {c : α →ₗ[ℝ] ℝ}
    (y : Fin P.m → ℝ) (z : Fin P.me → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hc : ∀ x : α, c x = (∑ i, y i * P.A i x) + ∑ i, z i * P.Ae i x) :
    SupportBound P.construct c :=
  SupportBound.mono (P.construct_eq_feasible).subset (SupportBound.ofDual y z hy hc)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
