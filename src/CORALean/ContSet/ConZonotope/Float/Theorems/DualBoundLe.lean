module

public import CORALean.ContSet.ConZonotope.Float.Operations.DualBound
public import CORALean.ContSet.ConZonotope.Real.Theorems.DualBoundLe
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The float dual bound is a lower bound

The clamped multipliers are not negative, so the real bound at them is below `wᵀ β`
(`Real.ConZonotope.dualBound_le`). The real `w + Cᵀ μ` lies between its two roundings, so its
absolute value is at most the larger of theirs; the sums are rounded up and the difference down,
so the stored bound is below the real one. The bound at zero is below `wᵀ β` on the box.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `w` – coefficients of the bounded form
* `lam` – multipliers
* `β` – factors

## Hypotheses
* `hβ` – the factors lie in the unit box
* `hC` – the factors satisfy the constraints the stored rows denote

## Conclusion
* the stored bound is at most `wᵀ β`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.dualBound_le (C : Mat 𝕋 p q) (d : Vec 𝕋 p) (w : Vec 𝕋 q) (lam : Vec 𝕋 p)
    (β : Vec ℝ q) (hβ : ∀ j, |β j| ≤ 1)
    (hC : ∀ i, ∑ j, toReal (C i j) * β j ≤ toReal (d i)) : -- --- CONCL ---
    toReal (ConZonotope.dualBound C d w lam) ≤ ∑ j, toReal (w j) * β j := by -- --- PROOF ---
  -- the multipliers as stored, clamped at zero
  set μ : Vec 𝕋 p := fun i => maximum (lam i) zero with hμ
  have hμ0 : ∀ i, 0 ≤ toReal (μ i) := fun i => by
    rw [hμ, toReal_maximum, toReal_zero]; exact le_max_right _ _
  show toReal (maximum (subDown (neg (sumUp fun j => maximum
      (absolute (addUp (w j) (sumUp fun i => mulUp (μ i) (C i j))))
      (absolute (addDown (w j) (sumDown fun i => mulDown (μ i) (C i j))))))
    (sumUp fun i => mulUp (μ i) (d i))) (neg (sumUp fun j => absolute (w j)))) ≤ _
  rw [toReal_maximum]
  refine max_le ?_ ?_
  · -- the real `w + Cᵀ μ` between its two roundings
    have hcoef : ∀ j, |toReal (w j) + ∑ i, toReal (μ i) * toReal (C i j)|
        ≤ toReal (maximum (absolute (addUp (w j) (sumUp fun i => mulUp (μ i) (C i j))))
          (absolute (addDown (w j) (sumDown fun i => mulDown (μ i) (C i j))))) := fun j => by
      have hup := le_trans (Finset.sum_le_sum fun i _ => mul_le_mulUp (μ i) (C i j))
        (sum_le_sumUp fun i => mulUp (μ i) (C i j))
      have hdown := le_trans (sumDown_le_sum fun i => mulDown (μ i) (C i j))
        (Finset.sum_le_sum fun i _ => mulDown_le_mul (μ i) (C i j))
      have h1 := add_le_addUp (w j) (sumUp fun i => mulUp (μ i) (C i j))
      have h2 := addDown_le_add (w j) (sumDown fun i => mulDown (μ i) (C i j))
      rw [toReal_maximum, toReal_absolute, toReal_absolute, max_comm]
      exact abs_le_max_abs_abs (by linarith) (by linarith)
    -- the sums rounded up, the difference down, then the real bound
    have hsum := le_trans (Finset.sum_le_sum fun j _ => hcoef j) (sum_le_sumUp _)
    have hd := le_trans (Finset.sum_le_sum fun i _ => mul_le_mulUp (μ i) (d i))
      (sum_le_sumUp fun i => mulUp (μ i) (d i))
    have hreal := Real.ConZonotope.dualBound_le (fun i j => toReal (C i j)) (fun i => toReal (d i))
      (fun j => toReal (w j)) (fun i => toReal (μ i)) β hμ0 hβ hC
    have hsub := subDown_le_sub (neg (sumUp fun j => maximum
      (absolute (addUp (w j) (sumUp fun i => mulUp (μ i) (C i j))))
      (absolute (addDown (w j) (sumDown fun i => mulDown (μ i) (C i j))))))
      (sumUp fun i => mulUp (μ i) (d i))
    rw [toReal_neg] at hsub
    unfold Real.ConZonotope.dualBound at hreal
    linarith
  · -- the bound at zero: each term at least minus its absolute value
    rw [toReal_neg]
    have hw := sum_le_sumUp fun j => absolute (w j)
    simp_rw [toReal_absolute] at hw
    have hbox : -(∑ j, |toReal (w j)|) ≤ ∑ j, toReal (w j) * β j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h := abs_mul (toReal (w j)) (β j)
      have hle : |toReal (w j)| * |β j| ≤ |toReal (w j)| :=
        mul_le_of_le_one_right (abs_nonneg _) (hβ j)
      linarith [neg_abs_le (toReal (w j) * β j)]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
