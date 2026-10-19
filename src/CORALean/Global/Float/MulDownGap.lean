module

public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A row scaled entrywise and rounded down, against the unit box

What rescaling the coefficients of a row costs: `a diag(r)` stored rounded down, `mulDown aⱼ rⱼ`,
is off from the exact product by at most the gap to the product rounded up, entry by entry, so
against a vector `δ` in the unit box the whole row is off by at most the gaps summed upward. And a
row read at `m + diag(r) δ` splits into the row at `m`, the stored row at `δ` and that rounding.
The float `HPolytope.rescaleCols` and `ConZonotope.rescale` pay exactly this, for the constraint
rows and the generators.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A product rounded down is off by at most the rounded gap to the one rounded up. -/
theorem mulDown_gap (a r : 𝕋) :
    |toReal a * toReal r - toReal (mulDown a r)|
      ≤ toReal (subUp (mulUp a r) (mulDown a r)) := by -- --- PROOF ---
  have h1 := mulDown_le_mul a r
  have h2 := mul_le_mulUp a r
  have h3 := sub_le_subUp (mulUp a r) (mulDown a r)
  rw [abs_le]
  constructor <;> linarith

/-- A row `a diag(r)` rounded down, against `|δ| ≤ 1`, is off by at most its summed gaps. -/
theorem abs_sum_mulDown_gap_le (a r : Vec 𝕋 h) (δ : Vec ℝ h) (hδ : ∀ j, |δ j| ≤ 1) :
    |∑ j, (toReal (a j) * toReal (r j) - toReal (mulDown (a j) (r j))) * δ j| ≤
      toReal (sumUp fun j => subUp (mulUp (a j) (r j)) (mulDown (a j) (r j))) := by -- --- PROOF ---
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_le_sumUp _))
  rw [abs_mul]
  calc _ ≤ toReal (subUp (mulUp (a j) (r j)) (mulDown (a j) (r j))) * 1 :=
        mul_le_mul (mulDown_gap _ _) (hδ j) (abs_nonneg _)
          (le_trans (abs_nonneg _) (mulDown_gap _ _))
    _ = _ := mul_one _

/-- A row against `m + diag(r) δ` splits into the row against `m`, the row rounded down against
`δ`, and the rounding against `δ`. -/
theorem sum_mul_affine_split (a m r : Vec 𝕋 h) (δ ξ : Vec ℝ h)
    (hξ : ∀ j, ξ j = toReal (m j) + toReal (r j) * δ j) : -- --- CONCL ---
    ∑ j, toReal (a j) * ξ j = ∑ j, toReal (a j) * toReal (m j)
      + ∑ j, toReal (mulDown (a j) (r j)) * δ j
      + ∑ j, (toReal (a j) * toReal (r j) - toReal (mulDown (a j) (r j)))
        * δ j := by -- --- PROOF ---
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hξ j]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
