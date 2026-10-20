module

public import CORALean.ContSet.Zonotope.Float.Operations.MethCReach
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `methCReach` bounds `H G β`

A point `G β` of the zonotope, `|β| ≤ 1`, is carried by `H` to a vector whose every coordinate is a
sum over the generators of an entry of `H G` times a coefficient: at most the sum of the entries'
magnitudes, each of which lies between its two directed dot products.

## Inputs
* `H` – candidate right inverse
* `G` – generator matrix
* `β` – factor vector
* `i` – coordinate

## Hypotheses
* `hβ` – factors in the unit box

## Conclusion
* coordinate of the transformed point is bounded by the reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.methCReach_bound (H : Mat 𝕋 n n) (G : Mat 𝕋 n h) {β : Vec ℝ h}
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin n) : -- --- CONCL ---
    |(toRealMat H *ᵥ fun l => ∑ j, toReal (G l j) * β j) i|
      ≤ toReal (Zonotope.methCReach H G) := by -- --- PROOF ---
  -- the product, regrouped by generator
  have hre : (toRealMat H *ᵥ fun l => ∑ j, toReal (G l j) * β j) i
      = ∑ j, (∑ l, toReal (H i l) * toReal (G l j)) * β j := by
    simp only [Matrix.mulVec, dotProduct, toRealMat, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hre]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (le_trans (sum_le_sumUp fun j => maximum (absolute (dotDown (H i) fun l => G l j))
      (absolute (dotUp (H i) fun l => G l j)))
    (le_maximumOver (fun i => sumUp fun j => maximum (absolute (dotDown (H i) fun l => G l j))
      (absolute (dotUp (H i) fun l => G l j))) i))
  -- the entry of `H G` between its two roundings, times a coefficient of magnitude at most one
  have hd := dotDown_le (H i) fun l => G l j
  have hu := le_dotUp (H i) fun l => G l j
  rw [abs_mul]
  refine le_trans (mul_le_of_le_one_right (abs_nonneg _) (hβ j)) ?_
  rw [toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs hd hu

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
