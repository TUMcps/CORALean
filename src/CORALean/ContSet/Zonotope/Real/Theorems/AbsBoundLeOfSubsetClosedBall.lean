module

public import CORALean.ContSet.Zonotope.Real.Operations.AbsBound
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# `absBound` is what a sup-norm ball around a zonotope has to reach

The converse of `subset_closedBall_of_absBound_le`, and the direction that
makes a stated outer ball tell you something about the generators: if the
zonotope sits inside the ball of radius `r`, then every coordinate's
`absBound` is at most `r`, not just some aggregate of them. The witness point
puts the sign of the centre on every generator at that coordinate, so it
attains `|x j| = Z.absBound j` exactly.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real number times its own sign is its absolute value. -/
theorem aux_mul_sign_eq_abs (x : ℝ) : x * (if 0 ≤ x then (1 : ℝ) else -1) = |x| := by
  split
  · rw [mul_one, abs_of_nonneg]; assumption
  · rw [mul_neg_one, abs_of_neg (not_le.mp (by assumption))]

/-- The sign used throughout, squared, is `1`. -/
theorem aux_sign_mul_self (x : ℝ) :
    (if 0 ≤ x then (1 : ℝ) else -1) * (if 0 ≤ x then (1 : ℝ) else -1) = 1 := by
  split <;> ring

/-- The sign's absolute value is always `1`. -/
theorem aux_abs_sign (x : ℝ) : |if 0 ≤ x then (1 : ℝ) else -1| = 1 := by
  split <;> norm_num


-- =======================================  MAIN THEOREM  ======================================= --

/-- A zonotope inside the ball of radius `r` has every coordinate's `absBound`
at most `r`: the point that puts the centre's own sign on every generator at
that coordinate attains `|x j| = absBound j` exactly, and the ball bounds it. -/
theorem Zonotope.absBound_le_of_subset_closedBall {Z : Zonotope (Vec ℝ n)} {r : ℝ}
    (h : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r) (j : Fin n) :
    Z.absBound j ≤ r := by -- --- PROOF ---
  -- `t` and `β` put the centre's own sign on every generator, `x` the point that names
  set t : ℝ := if 0 ≤ Z.c j then (1 : ℝ) else -1 with ht
  set β : Fin Z.h → ℝ := fun l => t * (if 0 ≤ Z.G l j then (1 : ℝ) else -1) with hβdef
  have hβ : ∀ l, |β l| ≤ 1 := fun l => by
    rw [hβdef, abs_mul, ht, aux_abs_sign, aux_abs_sign]; norm_num
  set x : Vec ℝ n := fun i => Z.c i + ∑ l, Z.G l i * β l with hxdef
  have hx : x ∈ Z.construct := Zonotope.mem_construct_iff.mpr ⟨β, hβ, fun i => rfl⟩
  have hxjeq : x j = Z.c j + ∑ l, Z.G l j * β l := rfl
  have htc : t * Z.c j = |Z.c j| := by rw [mul_comm, ht, aux_mul_sign_eq_abs]
  have hsum : t * ∑ l, Z.G l j * β l = ∑ l, |Z.G l j| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hβdef]
    calc t * (Z.G l j * (t * (if 0 ≤ Z.G l j then (1:ℝ) else -1)))
        = (t * t) * (Z.G l j * (if 0 ≤ Z.G l j then (1:ℝ) else -1)) := by ring
      _ = Z.G l j * (if 0 ≤ Z.G l j then (1:ℝ) else -1) := by rw [ht, aux_sign_mul_self, one_mul]
      _ = |Z.G l j| := aux_mul_sign_eq_abs _
  have hxj : t * x j = Z.absBound j := by rw [hxjeq, mul_add, htc, hsum, Zonotope.absBound]
  -- `x` sits in the stated ball, and `t * x j` is `absBound j` up to its own sign
  have hmem := h hx
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hxjb : |x j| ≤ r := by
    have h1 : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
    rw [Real.norm_eq_abs] at h1
    exact h1.trans hmem
  have heq : |Z.absBound j| = |x j| := by rw [← hxj, abs_mul, ht, aux_abs_sign, one_mul]
  have hnonneg : 0 ≤ Z.absBound j := by rw [Zonotope.absBound]; positivity
  rw [abs_of_nonneg hnonneg] at heq
  rw [heq]
  exact hxjb

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
