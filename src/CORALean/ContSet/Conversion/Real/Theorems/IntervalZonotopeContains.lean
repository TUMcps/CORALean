module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as a zonotope

CORA's `zonotope(interval)`: the centre, and one generator per coordinate
carrying that coordinate's radius. `n` generators, and no loss — a box is a
zonotope with axis-aligned generators.

The enclosing direction holds of every box. A box whose `sup` falls below its `inf`
denotes nothing, while the zonotope built from it denotes the box with the two
swapped, so equality, `zonotope_exact`, needs `inf ≤ sup`: that a box, an `ℓ∞` ball
in particular, is exactly one zonotope [1, Sec. VI-A (ℓ∞)].

## References

* [1] T. Gehr, M. Mirman, D. Drachsler-Cohen, P. Tsankov, S. Chaudhuri and M. Vechev. "AI2:
      Safety and Robustness Certification of Neural Networks with Abstract Interpretation".
      IEEE S&P 2018, pp. 3-18.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.zonotope_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.zonotope.construct := by -- --- PROOF ---
  intro x hx
  have hlo : ∀ j, I.inf j ≤ x j := fun j => (hx j).1
  have hhi : ∀ j, x j ≤ I.sup j := fun j => (hx j).2
  have hrad : ∀ j, 0 ≤ (I.sup j - I.inf j) / 2 := fun j => by linarith [hlo j, hhi j]
  -- where the coordinate sits relative to its centre, and zero where it has no width
  set β : Fin n → ℝ := fun j => if I.sup j = I.inf j then 0
    else (x j - (I.inf j + I.sup j) / 2) / ((I.sup j - I.inf j) / 2) with hβdef
  have hb1 : ∀ j, |β j| ≤ 1 := by
    intro j
    by_cases h : I.sup j = I.inf j
    · rw [hβdef]
      simp only [if_pos h, abs_zero]
      norm_num
    · have hd : 0 < (I.sup j - I.inf j) / 2 :=
        lt_of_le_of_ne (hrad j) fun hc => h (by linarith)
      rw [hβdef]
      simp only [if_neg h]
      rw [abs_div, abs_of_pos hd, div_le_one hd, abs_le]
      constructor <;> linarith [hlo j, hhi j]
  -- and that coefficient reproduces the coordinate, whether or not it has width
  have hb2 : ∀ j, (I.inf j + I.sup j) / 2 + β j * ((I.sup j - I.inf j) / 2) = x j := by
    intro j
    by_cases h : I.sup j = I.inf j
    · rw [hβdef]
      simp only [if_pos h, zero_mul, add_zero]
      linarith [hlo j, hhi j, h]
    · have hd : (I.sup j - I.inf j) / 2 ≠ 0 :=
        ne_of_gt (lt_of_le_of_ne (hrad j) fun hc => h (by linarith))
      rw [hβdef]
      simp only [if_neg h]
      field_simp
      ring
  -- the value: only the diagonal generator `i` reaches coordinate `i`
  refine ⟨β, hb1, ?_⟩
  funext i
  have hsum : (∑ j : Fin n, β j •
        (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
      = β i * ((I.sup i - I.inf i) / 2) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [Pi.smul_apply, smul_eq_mul, if_neg (Ne.symm hj), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  show x i = ((fun i => (I.inf i + I.sup i) / 2 : Vec ℝ n) + ∑ j : Fin n, β j •
    (fun i => if i = j then (I.sup i - I.inf i) / 2 else 0 : Vec ℝ n)) i
  rw [Pi.add_apply, hsum]
  exact (hb2 i).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
