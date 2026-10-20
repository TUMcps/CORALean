module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A spectrahedral shadow's interval hull

CORA's `interval(SpS)`: `interval.empty` for an empty set, otherwise per coordinate the range
`supportFunc_(SpS, eᵢ, 'range')` of the two semidefinite programs. Here the coordinate bounds are
the support values `-supportFunc(-eᵢ)` and `supportFunc(eᵢ)`, taken as reals: an unbounded
coordinate has an infinite support value, which a real `Interval` cannot carry, so the statements
assume `isBounded`. Then the box encloses the set (`SpectraShadow.interval_contains`) and is the
tightest one: each bound is the least upper (greatest lower) bound of the coordinate over a nonempty
set (`SpectraShadow.interval_isLUB`, `SpectraShadow.interval_isGLB`).

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* `hb` – shadow bounded

## Conclusion
* shadow is contained in its interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.interval_contains (S : SpectraShadow (Vec ℝ n))
    (hb : S.isBounded) : -- --- CONCL ---
    S.construct ⊆ S.interval.construct := by -- --- PROOF ---
  intro x hx
  -- a member makes the set nonempty, so the `interval.empty` branch is not taken
  have hne : S.construct ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  intro i
  simp only [SpectraShadow.interval, if_neg hnemp]
  -- both axis supports are finite reals, and bound the coordinate
  obtain ⟨hp, hm⟩ := hb i
  have e1 := S.supportFunc_eq_coe_toReal _ hne hp
  have e2 := S.supportFunc_eq_coe_toReal _ hne hm
  have h1 := S.le_supportFunc_of_mem (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) hx
  have h2 := S.le_supportFunc_of_mem (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) hx
  rw [e1] at h1
  rw [e2] at h2
  have h1' := EReal.coe_le_coe_iff.mp h1
  have h2' := EReal.coe_le_coe_iff.mp h2
  simp only [LinearMap.proj_apply, LinearMap.neg_apply] at h1' h2'
  constructor
  · show -(S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ))).toReal ≤ x i
    linarith
  · exact h1'

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
