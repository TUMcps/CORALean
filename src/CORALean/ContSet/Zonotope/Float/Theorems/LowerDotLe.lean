module

public import CORALean.ContSet.Zonotope.Float.Operations.LowerDot
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.lowerDot` is attained from below

For a zonotope whose error box is non-empty, some point of it has `aᵀx` at least `lowerDot`,
so `lowerDot` is at most the support function in direction `a`. The point is the one the
support formula names: each generator at the sign of `aᵀGⱼ`, and the error box at the end of
each coordinate that makes `aᵢ eᵢ` smallest — `lowerDot` rounds every term down, so it stays
below the value at that point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.lowerDot_le (Z : Zonotope (Vec 𝕋 n)) (a : Vec 𝕋 n)
    (hE : ∀ i, toReal (Z.I_error.inf i) ≤ toReal (Z.I_error.sup i)) :
    ∃ x ∈ Z.construct, toReal (Z.lowerDot a) ≤ ∑ i, toReal (a i) * x i := by -- --- PROOF ---
  -- the generator signs and the box corner the support formula names
  set s : Fin Z.h → ℝ := fun j => ∑ i, toReal (a i) * toReal (Z.G j i) with hs
  set β : Vec ℝ Z.h := fun j => if 0 ≤ s j then 1 else -1 with hβ
  set e : Vec ℝ n := fun i =>
    if toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    then toReal (Z.I_error.inf i) else toReal (Z.I_error.sup i) with he
  -- the signs are admissible coefficients, and the corner is in the box
  have hβ1 : ∀ j, |β j| ≤ 1 := fun j => by
    by_cases h : 0 ≤ s j <;> simp [hβ, h]
  have hsβ : ∀ j, s j * β j = |s j| := fun j => by
    by_cases h : 0 ≤ s j
    · simp [hβ, h, abs_of_nonneg h]
    · simp [hβ, h, abs_of_neg (not_le.mp h)]
  have hemem : e ∈ Z.I_error.construct := fun i => by
    show toReal (Z.I_error.inf i) ≤ e i ∧ e i ≤ toReal (Z.I_error.sup i)
    by_cases h : toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    · rw [show e i = toReal (Z.I_error.inf i) from if_pos h]; exact ⟨le_rfl, hE i⟩
    · rw [show e i = toReal (Z.I_error.sup i) from if_neg h]; exact ⟨hE i, le_rfl⟩
  set z : Vec ℝ n := fun i => toReal (Z.c i) + ∑ j, toReal (Z.G j i) * β j with hz
  refine ⟨z + e, ⟨z, Zonotope.mem_nominalSet_iff.mpr ⟨β, hβ1, fun i => rfl⟩, e, hemem, rfl⟩, ?_⟩
  -- the value at that point
  have hval : ∑ i, toReal (a i) * (z + e) i
      = ∑ i, toReal (a i) * toReal (Z.c i) + ∑ j, |s j| + ∑ i, toReal (a i) * e i := by
    -- the nominal part: the signs make each generator contribute its absolute value
    have h1 : ∑ i, toReal (a i) * z i
        = ∑ i, toReal (a i) * toReal (Z.c i) + ∑ j, |s j| := by
      calc ∑ i, toReal (a i) * z i
          = ∑ i, toReal (a i) * toReal (Z.c i)
            + ∑ i, ∑ j, toReal (a i) * toReal (Z.G j i) * β j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hz, mul_add, Finset.mul_sum]
            exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
        _ = _ := by
            rw [Finset.sum_comm]
            refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
            rw [← hsβ j, hs]
            simp only [Finset.sum_mul]
    calc ∑ i, toReal (a i) * (z + e) i
        = ∑ i, toReal (a i) * z i + ∑ i, toReal (a i) * e i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by simp [mul_add]
      _ = _ := by rw [h1]
  rw [hval]
  -- each term of `lowerDot` below its exact value
  have hc : toReal (dotDown a Z.c) ≤ ∑ i, toReal (a i) * toReal (Z.c i) := dotDown_le a Z.c
  -- the generators: `max(0, lo, -hi)` is below `|aᵀGⱼ|`
  have hg : toReal (sumDown fun j => maximum zero
      (maximum (dotDown a fun i => Z.G j i) (neg (dotUp a fun i => Z.G j i)))) ≤ ∑ j, |s j| := by
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => ?_)
    rw [toReal_maximum, toReal_maximum, toReal_neg, toReal_zero]
    have hlo := dotDown_le a fun i => Z.G j i
    have hhi := le_dotUp a fun i => Z.G j i
    refine max_le (abs_nonneg _) (max_le ?_ ?_)
    · exact le_trans hlo (le_abs_self _)
    · exact le_trans (neg_le_neg hhi) (neg_le_abs _)
  -- the box: the smaller end of each coordinate
  have hb : toReal (sumDown fun i => minimum (mulDown (a i) (Z.I_error.inf i))
      (mulDown (a i) (Z.I_error.sup i))) ≤ ∑ i, toReal (a i) * e i := by
    refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_)
    rw [toReal_minimum]
    by_cases h : toReal (a i) * toReal (Z.I_error.inf i) ≤ toReal (a i) * toReal (Z.I_error.sup i)
    · simp only [he, if_pos h]
      exact le_trans (min_le_left _ _) (mulDown_le_mul _ _)
    · simp only [he, if_neg h]
      exact le_trans (min_le_right _ _) (mulDown_le_mul _ _)
  unfold Zonotope.lowerDot
  refine le_trans (addDown_le_add _ _) ?_
  refine add_le_add (le_trans (addDown_le_add _ _) (add_le_add hc hg)) hb

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
