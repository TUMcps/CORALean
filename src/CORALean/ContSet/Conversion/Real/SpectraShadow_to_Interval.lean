module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.SpectraShadow_to_Interval

@[expose] public section

/-!
# A spectrahedral shadow's interval hull

CORA's `interval(SpS)`: `interval.empty` for an empty set, otherwise per coordinate the range
`supportFunc_(SpS, eᵢ, 'range')` of the two semidefinite programs, `[inf, sup]`. Here the
coordinate bounds are the support values `-supportFunc(-eᵢ)` and `supportFunc(eᵢ)`, taken as
reals: an unbounded coordinate has an infinite support value, which a real `Interval` cannot
carry, so the statements assume `isBounded`.

Under `isBounded` the box encloses the set (`SpectraShadow.interval_contains`) and is the
tightest one: each bound is the least upper (greatest lower) bound of the coordinate over the
set (`SpectraShadow.interval_isLUB`, `SpectraShadow.interval_isGLB`) for a nonempty set. That is
the interval hull, not an enclosure with slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A finite support value of a nonempty set is the real it reads as. -/
theorem SpectraShadow.aux_supportFunc_eq_coe_toReal {α : Type} [AddCommGroup α] [Module ℝ α]
    (S : SpectraShadow α) (c : α →ₗ[ℝ] ℝ) (hne : S.construct ≠ ∅)
    (hfin : S.supportFunc c ≠ ⊤) : S.supportFunc c = ((S.supportFunc c).toReal : ℝ) :=
  (EReal.coe_toReal hfin (fun h => hne ((S.supportFunc_eq_bot_iff c).mp h))).symm


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.interval_contains (S : SpectraShadow (Vec ℝ n)) (hb : S.isBounded) :
    S.construct ⊆ S.interval.construct := by -- --- PROOF ---
  intro x hx
  -- a member makes the set nonempty, so the `interval.empty` branch is not taken
  have hne : S.construct ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  intro i
  simp only [SpectraShadow.interval, if_neg hnemp]
  -- both axis supports are finite reals, and bound the coordinate
  obtain ⟨hp, hm⟩ := hb i
  have e1 := S.aux_supportFunc_eq_coe_toReal _ hne hp
  have e2 := S.aux_supportFunc_eq_coe_toReal _ hne hm
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

theorem SpectraShadow.interval_isLUB (S : SpectraShadow (Vec ℝ n)) (hb : S.isBounded)
    (hne : S.construct ≠ ∅) (i : Fin n) :
    IsLUB ((fun x : Vec ℝ n => x i) '' S.construct) (S.interval.sup i) := by -- --- PROOF ---
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  have e1 := S.aux_supportFunc_eq_coe_toReal _ hne (hb i).1
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

theorem SpectraShadow.interval_isGLB (S : SpectraShadow (Vec ℝ n)) (hb : S.isBounded)
    (hne : S.construct ≠ ∅) (i : Fin n) :
    IsGLB ((fun x : Vec ℝ n => x i) '' S.construct) (S.interval.inf i) := by -- --- PROOF ---
  have hnemp : ¬ S.representsa_emptySet := fun h => hne ((S.representsa_emptySet_iff).mp h)
  have e2 := S.aux_supportFunc_eq_coe_toReal _ hne (hb i).2
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
