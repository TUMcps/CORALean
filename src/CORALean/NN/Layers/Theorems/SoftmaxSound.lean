module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Operations.Softmax
public import CORALean.NN.Layers.Theorems.SoftmaxLeRawUpper
public import CORALean.NN.Layers.Theorems.Real.SoftmaxMemTightened
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.SoftmaxRawLowerLe
public import CORALean.NN.Layers.Theorems.SumEraseLeSumOffUp
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# What the softmax layer encloses

`Real.softmax`: the normalization at a raw lower bound of zero, which `softmax_nonneg` gives, the
rounded raw lower bound where `softmaxExpInRange` licenses it, and the rounded raw upper bound,
each end rounded outward on the way.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Float Float.IntervalOuter Float.OfInterval Float.FloatOps
  Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋]
  {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.softmax_sound (k : ℕ) :
    (Layer.softmax (S := S) (n := n) k).Sound Real.softmax := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox : ∀ i, toReal ((interval s).inf i) ≤ x i ∧ x i ≤ toReal ((interval s).sup i) :=
    interval_outer s hx
  set I := interval s with hI
  set ru : Vec ℝ n := fun i => toReal (softmaxRawUpper k I i) with hru
  refine ofInterval_outer _ fun i => ?_
  obtain ⟨hlo, hhi⟩ := Real.softmax_mem_tightened x (fun _ => 0) ru
    (fun i => Real.softmax_nonneg x i) (fun i => softmax_le_rawUpper k I hbox i) i
  constructor
  · -- the normalization, rounded down twice on the way
    have hsum := sum_erase_le_sumOffUp i fun j => softmaxRawUpper k I j
    have hsub := subDown_le_sub (one : 𝕋) (sumOffUp i fun j => softmaxRawUpper k I j)
    rw [toReal_one] at hsub
    have hmax : max (0:ℝ) (1 - ∑ j ∈ Finset.univ.erase i, ru j) ≤ Real.softmax x i := hlo
    show toReal (maximum (softmaxRawLower k I i)
        (maximum zero (subDown one (sumOffUp i fun j => softmaxRawUpper k I j))))
      ≤ Real.softmax x i
    rw [toReal_maximum, toReal_maximum, toReal_zero]
    exact max_le (softmaxRawLower_le k I hbox i)
      (max_le (le_trans (le_max_left _ _) hmax)
        (le_trans (by linarith) (le_trans (le_max_right _ _) hmax)))
  · -- `1` is what the same identity gives at a raw lower bound of zero
    have hone : (1:ℝ) - ∑ j ∈ Finset.univ.erase i, (0:ℝ) = 1 := by
      rw [Finset.sum_const_zero, sub_zero]
    rw [hone] at hhi
    show Real.softmax x i ≤ toReal (minimum (softmaxRawUpper k I i) one)
    rw [toReal_minimum, toReal_one]
    exact hhi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
