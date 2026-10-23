module

public import CORALean.ContSet.Interval.Float.Operations.ContractHalfspace

@[expose] public section

/-!
# `Interval.contractHalfspace` keeps every point of the box in the halfspace

The rest of the row is bounded term by term, each at the end its sign picks and
summed upward, so `a_j x_j ≤ c_j` holds at every point of the box meeting the
halfspace; dividing by a coefficient certified positive, or negated when
certified negative, rounds outward.

## Inputs
* `I` – interval box
* `a` – normal vector of the halfspace
* `b` – offset of the halfspace
* `x` – point of the box

## Hypotheses
* `hx` – `x` lies in the box
* `hab` – `x` satisfies the halfspace inequality

## Conclusion
* the point lies in the contracted box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.contractHalfspace_outer (I : Interval (Vec 𝕋 n)) (a : Vec 𝕋 n) (b : 𝕋)
    {x : Vec ℝ n} (hx : x ∈ I.construct)
    (hab : ∑ j, toReal (a j) * x j ≤ toReal b) : -- --- CONCL ---
    x ∈ (I.contractHalfspace a b).construct := by -- --- PROOF ---
  have hlo : ∀ k, toReal (I.inf k) ≤ x k := fun k => (hx k).1
  have hhi : ∀ k, x k ≤ toReal (I.sup k) := fun k => (hx k).2
  -- the rest of the row against the box, rounded upward
  set rest : Fin n → 𝕋 := fun j => sumUp fun k =>
    if k = j then zero else maximum (mulUp (neg (a k)) (I.sup k)) (mulUp (neg (a k)) (I.inf k))
      with hrest
  -- the row's own term, bounded by the rest of it over the box
  have hrow : ∀ j, toReal (a j) * x j ≤ toReal (addUp b (rest j)) := by
    intro j
    have hterm : ∀ k, (if k = j then (0 : ℝ) else -(toReal (a k) * x k)) ≤ toReal
        (if k = j then zero
          else maximum (mulUp (neg (a k)) (I.sup k)) (mulUp (neg (a k)) (I.inf k))) := by
      intro k
      -- the row's own entry is skipped, every other at the end its sign picks
      by_cases hk : k = j
      · simp only [if_pos hk, toReal_zero, le_refl]
      · simp only [if_neg hk]
        rw [toReal_maximum, ← neg_mul, ← toReal_neg]
        rcases le_total 0 (toReal (neg (a k))) with hs | hs
        · exact le_trans (le_trans (mul_le_mul_of_nonneg_left (hhi k) hs)
            (mul_le_mulUp _ _)) (le_max_left _ _)
        · exact le_trans (le_trans (mul_le_mul_of_nonpos_left (hlo k) hs)
            (mul_le_mulUp _ _)) (le_max_right _ _)
    -- summed upward, the rest of the row; then the row is its own term less the rest
    have hrest := le_trans (Finset.sum_le_sum fun k _ => hterm k) (sum_le_sumUp _)
    have hsplit : ∑ k, toReal (a k) * x k = toReal (a j) * x j
        - ∑ k, (if k = j then (0 : ℝ) else -(toReal (a k) * x k)) := by
      have h : ∀ k, toReal (a k) * x k = (if k = j then toReal (a k) * x k else 0)
          - (if k = j then (0 : ℝ) else -(toReal (a k) * x k)) := by
        intro k
        by_cases hk : k = j <;> simp [hk]
      rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp
    have hadd := add_le_addUp b (rest j)
    linarith
  intro j
  have hr := hrow j
  set C := addUp b (rest j) with hC
  constructor
  · -- the lower end moves only for a coefficient certified negative
    show toReal (if ltStrict (a j) zero then maximum (I.inf j) (neg (divUp C (neg (a j))))
      else I.inf j) ≤ x j
    split_ifs with hneg
    · have hn : 0 < toReal (neg (a j)) := by
        have := toReal_lt_of_ltStrict hneg
        rw [toReal_zero] at this
        rw [toReal_neg]
        linarith
      rw [toReal_maximum, max_le_iff]
      refine ⟨hlo j, ?_⟩
      have hd := div_le_divUp C (neg (a j)) hn
      have hq : -x j ≤ toReal C / toReal (neg (a j)) := by
        rw [le_div_iff₀ hn, toReal_neg]
        linarith
      rw [toReal_neg]
      linarith
    · exact hlo j
  · -- the upper end moves only for a coefficient certified positive
    show x j ≤ toReal (if ltStrict zero (a j) then minimum (I.sup j) (divUp C (a j)) else I.sup j)
    split_ifs with hpos
    · have hp : 0 < toReal (a j) := by
        have := toReal_lt_of_ltStrict hpos
        rwa [toReal_zero] at this
      rw [toReal_minimum, le_min_iff]
      refine ⟨hhi j, le_trans ?_ (div_le_divUp _ _ hp)⟩
      rw [le_div_iff₀ hp, mul_comm]
      exact hr
    · exact hhi j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
