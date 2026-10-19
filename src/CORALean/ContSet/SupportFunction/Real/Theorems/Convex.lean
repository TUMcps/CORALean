module

public import CORALean.ContSet.SupportFunction.Real.SupportFunction
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A support function denotes a convex set

The set is an intersection of halfspaces, one per direction. A direction in which the bound is `+∞`
excludes nothing, and one whose bound is `-∞` leaves no point at all.

## Inputs
* `S` – support function

## Hypotheses
* none

## Conclusion
* a support function denotes a convex set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SupportFunction.convex_construct (S : SupportFunction α) :
    Convex ℝ S.construct := by -- --- PROOF ---
  intro x hx y hy a b ha hb hab ℓ
  have hxd := hx ℓ
  have hyd := hy ℓ
  -- the bound under `ℓ`: `-∞` is impossible, `+∞` is trivial, a real one is linear
  generalize S.h ℓ = t at hxd hyd ⊢
  induction t using EReal.rec with
  | bot => exact absurd hxd (not_le.mpr (EReal.bot_lt_coe _))
  | top => exact le_top
  | coe r =>
    have h1 : ℓ x ≤ r := EReal.coe_le_coe_iff.mp hxd
    have h2 : ℓ y ≤ r := EReal.coe_le_coe_iff.mp hyd
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    refine EReal.coe_le_coe_iff.mpr ?_
    have hr : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
