import CORALean.ContSet.Conversion.Float.ContSet_to_Interval
import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.Global.Float.Exp
import CORALean.NN.Layers.Softmax

/-!
# The softmax layer over a floating-point scalar

The exact layer's box, with one bound missing and the normalization standing in
for it. A raw lower bound would ask for an *upper* bound on an exponential, and
`Global/Float`'s `expUp` carries a hypothesis on its argument that no total float
expression discharges — where a layer cannot carry a hypothesis, `propagate`
being total.

So this layer computes no raw lower bound. It passes `0`, which `softmax_nonneg`
justifies, and takes its lower bound from `y i ≥ 1 - ∑_{j≠i} ru j`, which needs
only the *upper* bounds and so only `expDown`. `Real.softmax_mem_tightened` was
stated for arbitrary raw bounds exactly so that this substitution costs nothing.
The upper bound stays sharp at `min (ru i) 1`, the `1` being what the same
identity gives at `rl = 0`.

The constraint the standard treatment throws away is therefore not a refinement
here: it is the only lower bound this layer has, and without it the enclosure
would be `[0, ru i]`. `k` is the reduction depth, precision alone as in `Sigmoid`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet IntervalOuter OfInterval FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-! ## Leaving one index out of a sum

`Fin n` has no index type for "everything but `i`", so a term is zeroed instead
and the exact layer's `Finset.erase` is met halfway. -/

private theorem toReal_ite_zero (v : Fin n → 𝕋) (i j : Fin n) :
    toReal (if j = i then zero else v j) = if j = i then (0 : ℝ) else toReal (v j) := by
  by_cases h : j = i
  · rw [if_pos h, if_pos h, toReal_zero]
  · rw [if_neg h, if_neg h]

private theorem sum_ite_zero (i : Fin n) (h : Fin n → ℝ) :
    ∑ j, (if j = i then (0 : ℝ) else h j) = ∑ j ∈ Finset.univ.erase i, h j := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => if j = i then (0 : ℝ) else h j)
    (Finset.mem_univ i), if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

private def sumOffUp (i : Fin n) (v : Fin n → 𝕋) : 𝕋 :=
  sumUp fun j => if j = i then zero else v j

private def sumOffDown (i : Fin n) (v : Fin n → 𝕋) : 𝕋 :=
  sumDown fun j => if j = i then zero else v j

/-- The zeroed term contributes nothing, so the sum is the erased one, rounded up. -/
private theorem sum_erase_le_sumOffUp (i : Fin n) (v : Fin n → 𝕋) :
    ∑ j ∈ Finset.univ.erase i, toReal (v j) ≤ toReal (sumOffUp i v) := by
  have h : ∑ j, toReal (if j = i then zero else v j)
      = ∑ j ∈ Finset.univ.erase i, toReal (v j) := by
    rw [Finset.sum_congr rfl fun j _ => toReal_ite_zero v i j]
    exact sum_ite_zero i fun j => toReal (v j)
  rw [← h]
  exact sum_le_sumUp _

/-- And downward against any real bound on the terms, which is what the layer has. -/
private theorem sumOffDown_le (i : Fin n) (v : Fin n → 𝕋) (h : Fin n → ℝ)
    (hv : ∀ j, j ≠ i → toReal (v j) ≤ h j) :
    toReal (sumOffDown i v) ≤ ∑ j ∈ Finset.univ.erase i, h j := by
  refine le_trans (sumDown_le_sum _) ?_
  rw [Finset.sum_congr rfl fun j _ => toReal_ite_zero v i j, ← sum_ite_zero i h]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    exact hv j hj

/-! ## The raw upper bound

`expDown` underestimates the denominator of `Real.softmax_eq_inv`, which
overestimates the quotient — the one direction available without a hypothesis on
the argument. -/

/-- Never below one, so `divUp` never meets a divisor `SoundFloatArithmetic`
says nothing about. -/
def softmaxDenomDown (k : ℕ) (I : Interval 𝕋 n) (i : Fin n) : 𝕋 :=
  maximum one (addDown one
    (sumOffDown i fun j => expDown k (subDown (I.inf j) (I.sup i))))

/-- An underestimated denominator, so the quotient is an overestimate. -/
def softmaxRawUpper (k : ℕ) (I : Interval 𝕋 n) (i : Fin n) : 𝕋 :=
  divUp one (softmaxDenomDown k I i)

private theorem one_le_softmaxDenomDown (k : ℕ) (I : Interval 𝕋 n) (i : Fin n) :
    1 ≤ toReal (softmaxDenomDown k I i) := by
  rw [softmaxDenomDown, toReal_maximum, toReal_one]
  exact le_max_left _ _

private theorem softmaxDenomDown_le (k : ℕ) (I : Interval 𝕋 n) (i : Fin n) :
    toReal (softmaxDenomDown k I i)
      ≤ 1 + ∑ j ∈ Finset.univ.erase i,
          Real.exp (toReal (I.inf j) - toReal (I.sup i)) := by
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

/-- An underestimated positive denominator gives an overestimated reciprocal,
and the rounding only grows it further. -/
private theorem one_div_le_divUp {d : 𝕋} {y : ℝ} (h1 : 1 ≤ toReal d) (h2 : toReal d ≤ y) :
    1 / y ≤ toReal (divUp one d) := by
  have hd : (0:ℝ) < toReal d := lt_of_lt_of_le zero_lt_one h1
  have hdiv := div_le_divUp one d hd
  rw [toReal_one] at hdiv
  exact le_trans (one_div_le_one_div_of_le hd h2) hdiv

theorem softmax_le_rawUpper (k : ℕ) (I : Interval 𝕋 n) {x : Vec ℝ n}
    (hx : ∀ i, toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i)) (i : Fin n) :
    Real.softmax x i ≤ toReal (softmaxRawUpper k I i) := by
  have hraw := Real.softmax_le_raw hx i
  rw [← one_div] at hraw
  exact le_trans hraw
    (one_div_le_divUp (one_le_softmaxDenomDown k I i) (softmaxDenomDown_le k I i))

/-! ## The layer -/

/-- The lower bound is the normalization and nothing else, the upper the raw
bound capped at one. -/
def softmaxBox (k : ℕ) (I : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i =>
    maximum zero (subDown one (sumOffUp i fun j => softmaxRawUpper k I j))
  sup := fun i => minimum (softmaxRawUpper k I i) one

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S 𝕋] [OfInterval S 𝕋]

noncomputable def Layer.softmax (k : ℕ) : Real.Layer S n n where
  eval := Real.softmax
  propagate s := ofInterval (softmaxBox k (interval s))
  propagate_outer s x hx := by
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
      show toReal (maximum zero (subDown one (sumOffUp i fun j => softmaxRawUpper k I j)))
        ≤ Real.softmax x i
      rw [toReal_maximum, toReal_zero]
      exact max_le (le_trans (le_max_left _ _) hmax)
        (le_trans (by linarith) (le_trans (le_max_right _ _) hmax))
    · -- `1` is what the same identity gives at a raw lower bound of zero
      have hone : (1:ℝ) - ∑ j ∈ Finset.univ.erase i, (0:ℝ) = 1 := by
        rw [Finset.sum_const_zero, sub_zero]
      rw [hone] at hhi
      show Real.softmax x i ≤ toReal (minimum (softmaxRawUpper k I i) one)
      rw [toReal_minimum, toReal_one]
      exact hhi

end CORALean.Float
