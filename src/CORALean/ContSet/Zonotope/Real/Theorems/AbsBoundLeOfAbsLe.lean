import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic.Positivity

/-!
# A coordinate's `absBound` is the largest `|x j|` a zonotope reaches

If every point of the zonotope has `|x j| ≤ r`, then `absBound j ≤ r`: the point that puts the
centre's own sign on every generator at that coordinate attains `|x j| = absBound j`. The
coordinatewise form of `absBound_le_of_subset_closedBall`, which asks the same of all coordinates
at one radius.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real number times its own sign is its absolute value. -/
theorem aux_absLe_mul_sign (x : ℝ) : x * (if 0 ≤ x then (1 : ℝ) else -1) = |x| := by
  split
  · rw [mul_one, abs_of_nonneg]; assumption
  · rw [mul_neg_one, abs_of_neg (not_le.mp (by assumption))]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.absBound_le_of_abs_le {Z : Zonotope (Vec ℝ n)} {r : ℝ} {j : Fin n}
    (h : ∀ x ∈ Z.construct, |x j| ≤ r) : Z.absBound j ≤ r := by -- --- PROOF ---
  -- the centre's sign on every generator at coordinate `j`
  set t : ℝ := if 0 ≤ Z.c j then (1 : ℝ) else -1 with ht
  set β : Fin Z.h → ℝ := fun l => t * (if 0 ≤ Z.G l j then (1 : ℝ) else -1) with hβdef
  have hβ : ∀ l, |β l| ≤ 1 := fun l => by
    rw [hβdef, ht]
    by_cases h1 : 0 ≤ Z.c j <;> by_cases h2 : 0 ≤ Z.G l j <;> simp [h1, h2]
  set x : Vec ℝ n := fun i => Z.c i + ∑ l, Z.G l i * β l with hxdef
  -- it is a point of the zonotope, and its `j`-th coordinate is the reach up to the sign
  have hx : x ∈ Z.construct := Zonotope.mem_construct_iff.mpr ⟨β, hβ, fun i => rfl⟩
  have htt : t * t = 1 := by rw [ht]; split <;> norm_num
  have htc : t * Z.c j = |Z.c j| := by rw [mul_comm, ht, aux_absLe_mul_sign]
  have hsum : t * ∑ l, Z.G l j * β l = ∑ l, |Z.G l j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hβdef]
    calc t * (Z.G l j * (t * (if 0 ≤ Z.G l j then (1:ℝ) else -1)))
        = (t * t) * (Z.G l j * (if 0 ≤ Z.G l j then (1:ℝ) else -1)) := by ring
      _ = |Z.G l j| := by rw [htt, one_mul, aux_absLe_mul_sign]
  have hxj : t * x j = Z.absBound j := by
    show t * (Z.c j + ∑ l, Z.G l j * β l) = _
    rw [mul_add, htc, hsum, Zonotope.absBound]
  have habs : |t| = 1 := by rw [ht]; split <;> norm_num
  have heq : |Z.absBound j| = |x j| := by rw [← hxj, abs_mul, habs, one_mul]
  have hnonneg : 0 ≤ Z.absBound j := by rw [Zonotope.absBound]; positivity
  rw [abs_of_nonneg hnonneg] at heq
  rw [heq]
  exact h x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
