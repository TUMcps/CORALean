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
# A spectrahedral shadow's interval hull: `interval_isLUB`

## Inputs
* `S` – spectrahedral shadow
* `i` – coordinate

## Hypotheses
* `hb` – shadow bounded
* `hne` – shadow nonempty

## Conclusion
* upper end is the least upper bound of the coordinate
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

theorem SpectraShadow.interval_isLUB (S : SpectraShadow (Vec ℝ n)) (hb : S.isBounded)
    (hne : S.construct ≠ ∅) (i : Fin n) : -- --- CONCL ---
    IsLUB ((fun x : Vec ℝ n => x i) '' S.construct) (S.interval.sup i) := by -- --- PROOF ---
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  have e1 := S.supportFunc_eq_coe_toReal _ hne (hb i).1
  have hs : S.interval.sup i = (S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)).toReal := by
    simp only [SpectraShadow.interval, if_neg hnemp]
  rw [hs]
  constructor
  · -- the support value is above every coordinate
    rintro _ ⟨x, hx, rfl⟩
    have h1 := S.le_supportFunc_of_mem (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) hx
    rw [e1] at h1
    exact EReal.coe_le_coe_iff.mp h1
  · -- and below every upper bound, being a supremum
    intro b hb'
    have : S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ) ≤ (b : EReal) :=
      S.supportFunc_le_of_bound _ ⟨b, fun x hx => hb' ⟨x, hx, rfl⟩⟩
    rw [e1] at this
    exact EReal.coe_le_coe_iff.mp this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
