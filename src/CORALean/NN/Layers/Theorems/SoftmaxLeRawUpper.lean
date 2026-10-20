module

public import CORALean.NN.Layers.Operations.SoftmaxRawUpper
public import CORALean.NN.Layers.Theorems.Real.SoftmaxLeRaw
public import CORALean.NN.Layers.Theorems.SumOffDownLe

@[expose] public section

/-!
# Softmax below its rounded raw upper bound

`Real.softmax_le_raw` at the box the stored bounds denote, the denominator underestimated
term by term through `expDown_le` and the reciprocal rounded up.

## Inputs
* `k` – reduction depth of the exponential
* `I` – box of the layer's input
* `x` – input vector
* `i` – output coordinate

## Hypotheses
* `hx` – the input lies in the box

## Conclusion
* the softmax is at most the rounded raw upper bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_one_le_softmaxDenomDown (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    1 ≤ toReal (softmaxDenomDown k I i) := by
  rw [softmaxDenomDown, toReal_maximum, toReal_one]
  exact le_max_left _ _

theorem aux_softmaxDenomDown_le (k : ℕ) (I : Interval (Vec 𝕋 n)) (i : Fin n) : -- --- CONCL ---
    toReal (softmaxDenomDown k I i)
      ≤ 1 + ∑ j ∈ Finset.univ.erase i,
          Real.exp (toReal (I.inf j) - toReal (I.sup i)) := by -- --- PROOF ---
  have hterm : ∀ j, j ≠ i →
      toReal (expDown k (subDown (I.inf j) (I.sup i)))
        ≤ Real.exp (toReal (I.inf j) - toReal (I.sup i)) := fun j _ =>
    le_trans (expDown_le k _) (Real.exp_le_exp.mpr (subDown_le_sub (I.inf j) (I.sup i)))
  -- the `maximum one` floor is the only place this could exceed the real denominator
  have hsum := sumOffDown_le i (fun j => expDown k (subDown (I.inf j) (I.sup i)))
    (fun j => Real.exp (toReal (I.inf j) - toReal (I.sup i))) hterm
  have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase i,
      Real.exp (toReal (I.inf j) - toReal (I.sup i)) :=
    Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
  have hadd := addDown_le_add (one : 𝕋)
    (sumOffDown i fun j => expDown k (subDown (I.inf j) (I.sup i)))
  rw [toReal_one] at hadd
  rw [softmaxDenomDown, toReal_maximum, toReal_one]
  exact max_le (by linarith) (by linarith)


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_le_rawUpper (k : ℕ) (I : Interval (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : ∀ i, toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i)) (i : Fin n) :
    Real.softmax x i ≤ toReal (softmaxRawUpper k I i) := by
  have hraw := Real.softmax_le_raw hx i
  rw [← one_div] at hraw
  exact le_trans hraw
    (one_div_le_divUp (aux_one_le_softmaxDenomDown k I i) (aux_softmaxDenomDown_le k I i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
