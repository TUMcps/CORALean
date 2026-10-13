import CORALean.ContDynamics.LinearARX.Operations.IdentifyBlocks
import CORALean.ContDynamics.LinearARX.Operations.IdentifyRegressor

/-!
# The blocks of a matrix act on the regressor as the ARX recursion

`[A B]` applied to the regressor of step `k` is `∑ A_i y(k-1-i) + ∑ B_j u(k-j)`, the right-hand
side of `LinearARX.Trajectory.step`: `identifyBlocks` cuts the columns where `identifyRegressor`
stacks them.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum over `Fin (p * d)` is the double sum over the blocks. -/
theorem aux_sum_finProd {p d : ℕ} (f : Fin (p * d) → ℝ) :
    ∑ r, f r = ∑ i : Fin p, ∑ b : Fin d, f (finProdFinEquiv (i, b)) := by
  rw [← Equiv.sum_comp finProdFinEquiv f, Fintype.sum_prod_type]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.identifyBlocks_mulVec (M : Mat ℝ dy (p * dy + (p + 1) * du))
    (y : ℕ → Vec ℝ dy) (u : ℕ → Vec ℝ du) (k : ℕ) :
    M *ᵥ LinearARX.identifyRegressor p y u k
      = ∑ i : Fin p, (LinearARX.identifyBlocks M).Abar i *ᵥ y (k - (i + 1))
        + ∑ j : Fin (p + 1), (LinearARX.identifyBlocks M).Bbar j *ᵥ u (k - j) := by -- --- PROOF ---
  funext a
  -- split the columns into the output part and the input part
  simp only [Matrix.mulVec, dotProduct, LinearARX.identifyRegressor, Pi.add_apply,
    Finset.sum_apply]
  rw [Fin.sum_univ_add (a := p * dy) (b := (p + 1) * du)]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  · rw [aux_sum_finProd (p := p) (d := dy)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    simp [LinearARX.identifyBlocks, NonlinearARX.pastOut]
  · rw [aux_sum_finProd (p := p + 1) (d := du)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [LinearARX.identifyBlocks, NonlinearARX.pastIn]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
