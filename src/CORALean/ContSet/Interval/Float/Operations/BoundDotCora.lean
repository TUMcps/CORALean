module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatBound

@[expose] public section

/-!
# `Interval.boundDotCora`

CORA's support function of a box in the direction `a`: `a' c + |a|' r`, the center
`c = (inf + sup) / 2` and the half-width `r = (sup - inf) / 2`. Each center term is the larger of
`a` times the center rounded up and rounded down, which bounds it whatever the sign of `a`, and the
half-width is rounded up. At `nearest` both centers are the machine's `(inf + sup) * 0.5`, so the
larger is that one product, and the value is CORA's bit for bit. The two sums are taken separately
and then added, as CORA's two products.

## Inputs
* `I` – interval box
* `c` – linear functional
* `a` – float coefficient vector of `c`

## Hypotheses
* `hc` – `c` is the dot product with `a`

## Output
* float upper bound of `c` on the box `I`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's support function of a box, `a' c + |a|' r`, each center term the larger of the two
roundings of the center and the half-width rounded up. -/
def Interval.boundDotCora (I : Interval (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) : FloatBound 𝕋 I.toSet c where
  val :=
    let up : Vec 𝕋 n := fun j => half (addUp (I.inf j) (I.sup j))     -- `(inf + sup) / 2`, up
    let dn : Vec 𝕋 n := fun j => half (addDown (I.inf j) (I.sup j))   -- and down
    let rad : Vec 𝕋 n := fun j => half (subUp (I.sup j) (I.inf j))    -- `(sup - inf) / 2`, up
    addUp (sumUp fun j => maximum (mulUp (a j) (up j)) (mulUp (a j) (dn j)))
      (sumUp fun j => mulUp (absolute (a j)) (rad j))
  le x hx := by
    rw [hc x]
    refine le_trans ?_ (add_le_addUp _ _)
    refine le_trans ?_ (add_le_add (sum_le_sumUp _) (sum_le_sumUp _))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hlo : toReal (I.inf j) ≤ x j := (hx j).1
    have hhi : x j ≤ toReal (I.sup j) := (hx j).2
    -- the half-width, rounded up, covers the distance to the true center
    have hr := sub_le_subUp (I.sup j) (I.inf j)
    have hm := mul_le_mulUp (absolute (a j)) (half (subUp (I.sup j) (I.inf j)))
    rw [toReal_absolute, toReal_half] at hm
    have hrr : |toReal (a j)| * ((toReal (I.sup j) - toReal (I.inf j)) / 2) ≤
        |toReal (a j)| * (toReal (subUp (I.sup j) (I.inf j)) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    -- the distance to the true center, weighted by `a`
    have hd : toReal (a j) * (x j - (toReal (I.inf j) + toReal (I.sup j)) / 2) ≤
        |toReal (a j)| * ((toReal (I.sup j) - toReal (I.inf j)) / 2) := by
      refine le_trans (le_abs_self _) ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith
    rw [mul_sub] at hd
    rw [toReal_maximum]
    -- the center the sign of `a` needs: up for `a ≥ 0`, down for `a ≤ 0`
    have hc0 : toReal (a j) * ((toReal (I.inf j) + toReal (I.sup j)) / 2) ≤
        max (toReal (mulUp (a j) (half (addUp (I.inf j) (I.sup j)))))
          (toReal (mulUp (a j) (half (addDown (I.inf j) (I.sup j))))) := by
      rcases le_total 0 (toReal (a j)) with h0 | h0
      · have hu := add_le_addUp (I.inf j) (I.sup j)
        have hc1 := mul_le_mulUp (a j) (half (addUp (I.inf j) (I.sup j)))
        rw [toReal_half] at hc1
        have : toReal (a j) * ((toReal (I.inf j) + toReal (I.sup j)) / 2) ≤
            toReal (a j) * (toReal (addUp (I.inf j) (I.sup j)) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) h0
        exact le_trans (le_trans this hc1) (le_max_left _ _)
      · have hdn := addDown_le_add (I.inf j) (I.sup j)
        have hc1 := mul_le_mulUp (a j) (half (addDown (I.inf j) (I.sup j)))
        rw [toReal_half] at hc1
        have : toReal (a j) * ((toReal (I.inf j) + toReal (I.sup j)) / 2) ≤
            toReal (a j) * (toReal (addDown (I.inf j) (I.sup j)) / 2) :=
          mul_le_mul_of_nonpos_left (by linarith) h0
        exact le_trans (le_trans this hc1) (le_max_right _ _)
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
