module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SupportFunc

@[expose] public section

/-!
# `SpectraShadow.representsa_point`

CORA's `@spectraShadow/representsa_` at type `point`: it takes a feasible point `p`
(`priv_findFeasiblePointSpectrahedron`), shifts the set by it and asks `origin`. Here `p` is any
member whose coordinates are the supports, the same test for the one point CORA would find on a
singleton.

## Inputs
* `S` – spectrahedral shadow

## Output
* A member whose coordinates are the support values, from above and from below
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

/-- A member whose coordinates are the support values, from above and from below. -/
noncomputable def SpectraShadow.representsa_point (S : SpectraShadow (Vec ℝ n)) : Prop :=
  ∃ p ∈ S.construct, ∀ i : Fin n,
    S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) = ((p i : ℝ) : EReal)
      ∧ S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) = ((-p i : ℝ) : EReal)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
