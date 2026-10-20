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
# A spectrahedral shadow's interval hull: `interval_isGLB`

## Inputs
* `S` – spectrahedral shadow
* `i` – coordinate

## Hypotheses
* `hb` – shadow bounded
* `hne` – shadow nonempty

## Conclusion
* lower end is the greatest lower bound of the coordinate
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

theorem SpectraShadow.interval_isGLB (S : SpectraShadow (Vec ℝ n)) (hb : S.isBounded)
    (hne : S.construct ≠ ∅) (i : Fin n) :
    IsGLB ((fun x : Vec ℝ n => x i) '' S.construct) (S.interval.inf i) := by -- --- PROOF ---
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  have e2 := S.supportFunc_eq_coe_toReal _ hne (hb i).2
  have hs : S.interval.inf i
      = -(S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ))).toReal := by
    simp only [SpectraShadow.interval, if_neg hnemp]
  rw [hs]
  constructor
  · -- the negated support is below every coordinate
    rintro _ ⟨x, hx, rfl⟩
    have h2 := S.le_supportFunc_of_mem (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) hx
    rw [e2] at h2
    have := EReal.coe_le_coe_iff.mp h2
    simp only [LinearMap.neg_apply, LinearMap.proj_apply] at this
    linarith
  · -- and above every lower bound
    intro b hb'
    have : S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)) ≤ ((-b : ℝ) : EReal) :=
      S.supportFunc_le_of_bound _ ⟨-b, fun x hx => by
        have := hb' ⟨x, hx, rfl⟩
        simp only [LinearMap.neg_apply, LinearMap.proj_apply]
        linarith⟩
    rw [e2] at this
    have := EReal.coe_le_coe_iff.mp this
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
